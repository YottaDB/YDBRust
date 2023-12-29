/****************************************************************
*                                                               *
* Copyright (c) 2019-2023 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

//! This is the main implementation of the YDBRust wrapper.
//!
//! The API is not particularly friendly, but it exposes only safe code.
//!
//! Most operations are encapsulated in methods on the [`Key`] struct, and generally
//! consume a `Vec<u8>` and return [`YDBResult<Vec<u8>>`][YDBResult]. The return `Vec<u8>` will either contain
//! the data fetched from the database or an error.
//!
//! The `Vec<u8>` may be resized as part of the call.

pub mod call_in;

use std::{error::Error, marker::PhantomData};
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::ptr;
use std::ffi::CString;
use std::os::raw::{c_void, c_int};
use std::time::Duration;
use std::cmp::min;
use std::fmt;
use std::error;
use std::mem;
use std::panic;
use crate::craw::{
    ydb_buffer_t, ydb_get_st, ydb_set_st, ydb_data_st, ydb_delete_st, ydb_message_t, ydb_incr_st,
    ydb_node_next_st, ydb_node_previous_st, ydb_subscript_next_st, ydb_subscript_previous_st,
    ydb_tp_st, YDB_OK, YDB_ERR_INVSTRLEN, YDB_ERR_INSUFFSUBS, YDB_ERR_TPRETRY, YDB_DEL_TREE,
    YDB_DEL_NODE, YDB_TP_RESTART, YDB_TP_ROLLBACK,
};

const DEFAULT_CAPACITY: usize = 50;

/// An error returned by the underlying YottaDB library.
///
/// This error cannot be constructed manually.
#[derive(Clone, Hash, Eq, PartialEq)]
pub struct YDBError {
    /// YottaDB internally uses an error-handling mechanism similar to `errno` and `perror`.
    /// Since, in a threaded context, another error may occur before the application has
    /// a chance to call `perror()` (in YottaDB, [`$ZSTATUS`]),
    /// the stringified error must be returned at the same time as the status code.
    ///
    /// [`$ZSTATUS`]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#zstatus
    pub message: Vec<u8>,
    /// The status returned by a YottaDB function. This will be a `YDB_ERR_*` constant.
    ///
    /// ## See also
    /// - [ZMessage Codes](https://docs.yottadb.com/MessageRecovery/errormsgref.html#zmessage-codes)
    pub status: i32,
    /// The [transaction] that was in process when the error occurred.
    ///
    /// [transaction]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing
    tptoken: TpToken,
}

impl fmt::Debug for YDBError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "YDB Error ({}): {}", self.status, String::from_utf8_lossy(&self.message))
    }
}

impl fmt::Display for YDBError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp;
        let message = match message_t(self.tptoken, Vec::new(), self.status) {
            Ok(buf) => {
                tmp = buf;
                String::from_utf8_lossy(&tmp)
            }
            Err(err) => {
                std::borrow::Cow::from(format!("<error retrieving error message: {}>", err.status))
            }
        };
        write!(f, "YDB Error ({}): {}", message, &String::from_utf8_lossy(&self.message))
    }
}

impl error::Error for YDBError {}

/// A specialized `Result` type returned by a YottaDB function.
pub type YDBResult<T> = Result<T, YDBError>;

/// A transaction processing token, used by yottadb to ensure ACID properties.
///
/// The only valid values for a TpToken are the default (`TpToken::default()`)
/// or a token passed in from [`Context::tp`](crate::Context::tp).
///
/// TpTokens can be converted to `u64`, but not vice-versa.
#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct TpToken(
    // This is private to prevent users creating their own TpTokens. YDB has unpredictable behavior
    // when passed the wrong tptoken, such as infinite loops and aborts.
    pub(crate) u64,
);

impl fmt::Debug for TpToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let token: &dyn fmt::Display = if self.0 == 0 { &"YDB_NOTTP" } else { &self.0 };
        write!(f, "TpToken({})", token)
    }
}

impl Default for TpToken {
    fn default() -> Self {
        TpToken(crate::craw::YDB_NOTTP)
    }
}

impl From<TpToken> for u64 {
    /// This is useful for calling C functions that have not yet been wrapped in the `simple_api`
    /// from inside a transaction.
    ///
    /// # Example
    /// ```
    /// use yottadb::*;
    /// use yottadb::craw::ydb_buffer_t;
    /// Context::new().tp(|ctx| {
    ///   let tptoken_raw = u64::from(ctx.tptoken());
    ///   let mut errstr = ydb_buffer_t {
    ///     buf_addr: std::ptr::null_mut(),
    ///     len_alloc: 0,
    ///     len_used: 0,
    ///   };
    ///   unsafe { craw::ydb_stdout_stderr_adjust_t(tptoken_raw, &mut errstr) };
    ///   Ok(TransactionStatus::Ok)
    /// }, "BATCH", &[]);
    /// ```
    fn from(tptoken: TpToken) -> u64 {
        tptoken.0
    }
}

/// The type of data available at the current node.
///
/// # See also
/// - [`KeyContext::data()`](crate::KeyContext::data)
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum DataReturn {
    /// There is no data present, either here or lower in the tree.
    NoData,
    /// There is data present at this node, but not lower in the tree.
    ValueData,
    /// There is data present lower in the tree, but not at this node.
    TreeData,
    /// There is data present both at this node and lower in the tree.
    ValueTreeData,
}

/// The type of deletion that should be carried out.
///
/// # See also
/// - [`KeyContext::delete_st()`](crate::KeyContext::delete)
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum DeleteType {
    /// Delete only this node.
    DelNode,
    /// Delete this node and all subnodes in the tree.
    DelTree,
}

/// Provides a [`Key`] object for the given subscripts.
///
/// See [the YottaDB documentation][nodes-and-variables] for more information
/// about how YottaDB handles keys.
///
/// # Examples
///
/// Make a simple key:
/// ```
/// # #[macro_use] extern crate yottadb;
/// let my_key = make_key!("^MyTimeSeriesData", "5");
/// ```
///
/// Keys must have at least one variable:
/// ```compile_fail
/// let mut key = make_key!();
/// ```
///
/// [nodes-and-variables]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#keys-values-nodes-variables-and-subscripts
#[macro_export]
macro_rules! make_key {
    ( $var:expr $(,)? ) => (
        $crate::Key::variable($var)
    );
    ( $var: expr $( , $subscript: expr)+ $(,)? ) => (
        $crate::Key::new($var, &[
            $($subscript),*
        ])
    );
}

/// A key used to get, set, and delete values in the database.
///
/// # See also
/// - [`KeyContext`](super::context_api::KeyContext)
/// - [Keys, values, nodes, variables, and subscripts](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#keys-values-nodes-variables-and-subscripts)
/// - [Local and Global variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#local-and-global-variables)
/// - [Intrinsic special variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#intrinsic-special-variables)
#[derive(Clone, Hash, Eq, PartialEq)]
pub struct Key {
    /// The [variable] of the key, which can be freely modified.
    ///
    /// Note that not all variables are valid.
    /// If a `variable` is set to an invalid value, the next call to YottaDB
    /// will result in a [`YDB_ERR_INVVARNAME`](super::craw::YDB_ERR_INVVARNAME).
    /// See [variables vs. subscripts][variable] for details on what variables are valid and invalid.
    ///
    /// [variable]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#variables-vs-subscripts-vs-values
    pub variable: String,
    subscripts: Vec<Vec<u8>>,
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use std::fmt::Write;

        f.write_str(&self.variable)?;
        if let Some(first) = self.subscripts.first() {
            write!(f, "({:?}", String::from_utf8_lossy(first))?;
            for subscript in &self.subscripts[1..] {
                write!(f, ", {:?}", String::from_utf8_lossy(subscript))?;
            }
            f.write_char(')')?;
        }
        Ok(())
    }
}

impl Key {
    // public for `make_ckey!`
    #[doc(hidden)]
    /// Create a new key.
    pub fn new<V, S>(variable: V, subscripts: &[S]) -> Key
    where
        V: Into<String>,
        S: Into<Vec<u8>> + Clone,
    {
        Key {
            variable: variable.into(),
            // NOTE: we cannot remove this copy because `node_next_st` mutates subscripts
            // and `node_subscript_st` mutates the variable
            subscripts: subscripts.iter().cloned().map(|slice| slice.into()).collect(),
        }
    }

    // public for `make_ckey!`
    #[doc(hidden)]
    /// Shortcut for creating a key with no subscripts.
    pub fn variable<V: Into<String>>(var: V) -> Key {
        Key::new::<V, Vec<u8>>(var, &[])
    }

    /// Gets the value of this key from the database and returns the value.
    ///
    /// See also [KeyContext::get](crate::context_api::KeyContext::get).
    #[inline]
    pub(crate) fn get_st(&self, tptoken: TpToken, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.direct_unsafe_call(tptoken, out_buffer, ydb_get_st)
    }

    /// Sets the value of a key in the database.
    ///
    /// See also [KeyContext::set](crate::context_api::KeyContext::set).
    pub(crate) fn set_st<U>(
        &self, tptoken: TpToken, err_buffer: Vec<u8>, new_val: U,
    ) -> YDBResult<Vec<u8>>
    where
        U: AsRef<[u8]>,
    {
        let new_val = new_val.as_ref();
        let new_val_t = ydb_buffer_t {
            buf_addr: new_val.as_ptr() as *const _ as *mut _,
            len_alloc: new_val.len() as u32,
            len_used: new_val.len() as u32,
        };
        let do_call = |tptoken, out_buffer_p, varname_p, len, subscripts_p| unsafe {
            ydb_set_st(tptoken, out_buffer_p, varname_p, len, subscripts_p, &new_val_t)
        };
        self.non_allocating_call(tptoken, err_buffer, do_call)
    }

    /// Returns information about a local or global variable node.
    ///
    /// See also [KeyContext::data](crate::context_api::KeyContext::data).
    pub(crate) fn data_st(
        &self, tptoken: TpToken, err_buffer: Vec<u8>,
    ) -> YDBResult<(DataReturn, Vec<u8>)> {
        let mut retval: u32 = 0;
        let do_call = |tptoken, out_buffer_p, varname_p, len, subscripts_p| unsafe {
            ydb_data_st(tptoken, out_buffer_p, varname_p, len, subscripts_p, &mut retval as *mut _)
        };
        let err_buffer = self.non_allocating_call(tptoken, err_buffer, do_call)?;
        let data_ret = match retval {
            0 => DataReturn::NoData,
            1 => DataReturn::ValueData,
            10 => DataReturn::TreeData,
            11 => DataReturn::ValueTreeData,
            // If it's not one of these values, there is something wrong with the API
            //  and we need to address it. Returning an Err here won't make things
            //  more clear because the error code is not one of YottaDB's
            _ => panic!(
                "Unexpected return from ydb_data_st: {}, ZSTATUS: {}",
                retval,
                String::from_utf8_lossy(&err_buffer)
            ),
        };
        Ok((data_ret, err_buffer))
    }

    /// Delete nodes in the local or global variable tree or subtree specified.
    ///
    /// See also [KeyContext::delete](crate::context_api::KeyContext::delete).
    pub(crate) fn delete_st(
        &self, tptoken: TpToken, err_buffer: Vec<u8>, delete_type: DeleteType,
    ) -> YDBResult<Vec<u8>> {
        let c_delete_ty = match delete_type {
            DeleteType::DelNode => YDB_DEL_NODE,
            DeleteType::DelTree => YDB_DEL_TREE,
        } as i32;
        self.non_allocating_call(
            tptoken,
            err_buffer,
            |tptoken, out_buffer_p, varname_p, len, subscripts_p| unsafe {
                ydb_delete_st(tptoken, out_buffer_p, varname_p, len, subscripts_p, c_delete_ty)
            },
        )
    }

    // A call that can reallocate the `out_buffer`, but cannot modify `self`.
    //
    // `non_allocating_call` assumes that there are no extant references to `out_buffer`.
    // Functions that require a separate `err_buffer_t` cannot use `non_allocating_call`.
    //
    // `non_allocating_call` assumes that on error, `func` should be called again.
    // Functions which require `func` to only be called once cannot use `non_allocating_call`.
    fn non_allocating_call<F>(
        &self, tptoken: TpToken, err_buffer: Vec<u8>, mut func: F,
    ) -> YDBResult<Vec<u8>>
    where
        F: FnMut(u64, *mut ydb_buffer_t, *const ydb_buffer_t, i32, *const ydb_buffer_t) -> c_int,
    {
        self.non_allocating_ret_call(
            tptoken,
            err_buffer,
            |tptoken, err_buffer_p, varname_p, len, subscripts_p, out_buffer_p| {
                let status = func(tptoken, err_buffer_p, varname_p, len, subscripts_p);
                unsafe {
                    (*out_buffer_p).len_used = (*err_buffer_p).len_used;
                }
                status
            },
        )
    }

    // A call that can reallocate the `out_buffer`, but cannot modify `self`.
    //
    // `non_allocating_ret_call` assumes that there are no extant references to `out_buffer`.
    //
    // `non_allocating_ret_call` assumes that on error, `func` should be called again.
    // Functions which require `func` to only be called once cannot use `non_allocating_ret_call`.
    //
    // This differs from `non_allocating_call` in that it passes an `err_buffer_t` to the closure.
    fn non_allocating_ret_call<F>(
        &self, tptoken: TpToken, out_buffer: Vec<u8>, mut func: F,
    ) -> YDBResult<Vec<u8>>
    where
        F: FnMut(
            u64,
            *mut ydb_buffer_t,
            *const ydb_buffer_t,
            i32,
            *const ydb_buffer_t,
            *mut ydb_buffer_t,
        ) -> c_int,
    {
        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        // Finally make the `unsafe` call
        resize_ret_call(tptoken, out_buffer, |tptoken, err_buffer_p, out_buffer_p| {
            func(
                tptoken,
                err_buffer_p,
                varname.as_ptr(),
                subscripts.len() as i32,
                subscripts.as_ptr() as *const _,
                out_buffer_p,
            )
        })
    }

    /// Converts the value to a number and increments it based on the value specifed by `increment`.
    ///
    /// See also [KeyContext::increment](crate::context_api::KeyContext::increment).
    pub(crate) fn incr_st(
        &self, tptoken: TpToken, out_buffer: Vec<u8>, increment: Option<&[u8]>,
    ) -> YDBResult<Vec<u8>> {
        let mut increment_t_buf;
        let increment_p = if let Some(increment_v) = increment {
            increment_t_buf = ydb_buffer_t {
                buf_addr: increment_v.as_ptr() as *const _ as *mut _,
                len_alloc: increment_v.len() as u32,
                len_used: increment_v.len() as u32,
            };
            &mut increment_t_buf as *mut _
        } else {
            ptr::null_mut()
        };
        let mut first_run = true;
        let do_call = |tptoken, err_buffer_p, varname_p, len, subscripts_p, out_buffer_p| {
            if first_run {
                first_run = false;
                unsafe {
                    ydb_incr_st(
                        tptoken,
                        err_buffer_p,
                        varname_p,
                        len,
                        subscripts_p,
                        increment_p,
                        out_buffer_p,
                    )
                }
            } else {
                unsafe {
                    ydb_get_st(tptoken, err_buffer_p, varname_p, len, subscripts_p, out_buffer_p)
                }
            }
        };
        self.non_allocating_ret_call(tptoken, out_buffer, do_call)
    }

    /// Decrement the count of a lock held by the process.
    ///
    /// See also [KeyContext::lock_decr](crate::context_api::KeyContext::lock_decr).
    #[inline]
    pub(crate) fn lock_decr_st(&self, tptoken: TpToken, err_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        use crate::craw::ydb_lock_decr_st;
        let do_call = |tptoken, err_buffer_p, varname_p, len, subscripts_p| unsafe {
            ydb_lock_decr_st(tptoken, err_buffer_p, varname_p, len, subscripts_p)
        };
        self.non_allocating_call(tptoken, err_buffer, do_call)
    }

    /// Increment the count of a lock held by the process, or acquire a new lock.
    ///
    /// See also [KeyContext::lock_incr](crate::context_api::KeyContext::lock_incr).
    pub(crate) fn lock_incr_st(
        &self, tptoken: TpToken, mut err_buffer: Vec<u8>, timeout: Duration,
    ) -> YDBResult<Vec<u8>> {
        use std::convert::TryInto;
        use crate::craw::{ydb_lock_incr_st, YDB_ERR_TIME2LONG};

        let timeout_ns = match timeout.as_nanos().try_into() {
            Err(_) => {
                // discard any previous error
                err_buffer.clear();
                return Err(YDBError { status: YDB_ERR_TIME2LONG, message: err_buffer, tptoken });
            }
            Ok(n) => n,
        };
        let do_call = |tptoken, err_buffer_p, varname_p, len, subscripts_p| unsafe {
            ydb_lock_incr_st(tptoken, err_buffer_p, timeout_ns, varname_p, len, subscripts_p)
        };
        self.non_allocating_call(tptoken, err_buffer, do_call)
    }

    /// Facilitates depth-first traversal of a local or global variable tree, and passes itself in as the output parameter.
    ///
    /// See also [KeyContext::next_node_self](crate::context_api::KeyContext::next_node_self).
    #[inline]
    pub(crate) fn node_next_self_st(
        &mut self, tptoken: TpToken, out_buffer: Vec<u8>,
    ) -> YDBResult<Vec<u8>> {
        self.growing_shrinking_call(tptoken, out_buffer, ydb_node_next_st)
    }

    /// Facilitates reverse depth-first traversal of a local or global variable tree and reports the predecessor node, passing itself in as the output parameter.
    ///
    /// See also [KeyContext::next_prev_self](crate::context_api::KeyContext::next_).
    #[inline]
    pub(crate) fn node_prev_self_st(
        &mut self, tptoken: TpToken, out_buffer: Vec<u8>,
    ) -> YDBResult<Vec<u8>> {
        self.growing_shrinking_call(tptoken, out_buffer, ydb_node_previous_st)
    }

    /// A call that can change the number of subscripts (i.e. can return YDB_ERR_INSUFFSUBS).
    ///
    /// Most functions can only return YDB_ERR_INVSTRLEN if the subscripts don't have enough capacity
    /// reserved, so the error handling for them is much simpler. This has error handling for
    /// INSUFFSUBS, but is more complicated as a result, so it's only used where necessary.
    fn growing_shrinking_call(
        &mut self, tptoken: TpToken, mut err_buffer: Vec<u8>,
        c_func: unsafe extern "C" fn(
            // tptoken
            u64,
            // err_buffer_t
            *mut ydb_buffer_t,
            // varname
            *const ydb_buffer_t,
            // subs_used
            c_int,
            // `subsarray`, not a single subscript
            *const ydb_buffer_t,
            // ret_subs_used
            *mut c_int,
            // `ret_subsarray`, not a single subscript
            *mut ydb_buffer_t,
        ) -> c_int,
    ) -> YDBResult<Vec<u8>> {
        let subs_used = self.subscripts.len() as i32;
        let mut err_buffer_t = Self::make_out_buffer_t(&mut err_buffer);

        // this is a loop instead of a recursive call so we can keep the original `subs_used`
        let (ret_subs_used, buffer_structs) = loop {
            // Make sure `subscripts` is not a null pointer
            if self.subscripts.capacity() == 0 {
                self.subscripts.reserve(1);
            }

            // Get pointers to the varname and to the first subscript
            let (varname, mut subscripts) = self.get_buffers_mut();
            assert_eq!(subscripts.len(), self.subscripts.len());
            let mut ret_subs_used = subscripts.len() as i32;

            // Do the call
            let status = unsafe {
                c_func(
                    tptoken.0,
                    &mut err_buffer_t,
                    &varname,
                    subs_used,
                    subscripts.as_ptr(),
                    &mut ret_subs_used as *mut _,
                    subscripts.as_mut_ptr(),
                )
            };
            let ret_subs_used = ret_subs_used as usize;
            // Handle resizing the buffer, if needed
            // HACK: by reading the source, I saw that YDB will never return INVSTRLEN
            // for the `err_buffer`, only for the subscripts (it will just not write as long a message).
            // So it's ok for this to only look at the subscripts.
            if status == YDB_ERR_INVSTRLEN {
                let last_sub_index = ret_subs_used;
                assert!(last_sub_index < self.subscripts.len());

                let t = &mut self.subscripts[last_sub_index];
                let needed_size = subscripts[last_sub_index].len_used as usize;
                t.reserve(needed_size - t.len());
                assert_ne!(t.as_ptr(), std::ptr::null());

                continue;
            }
            if status == YDB_ERR_INSUFFSUBS {
                self.subscripts.resize_with(ret_subs_used, || Vec::with_capacity(10));
                continue;
            }
            // NOTE: `ret_subs_used` and `subscripts` came from references, so they can't be null.
            if status == crate::craw::YDB_ERR_PARAMINVALID {
                let i = ret_subs_used;
                panic!(
                    "internal error in node_prev_st: subscripts[{}] was null: {:?}",
                    i, subscripts[i]
                );
            }
            // Set length of the vec containing the buffer so we can see the value
            if status != YDB_OK as i32 {
                // We could end up with a buffer of a larger size if we couldn't fit the error string
                // into the out_buffer, so make sure to pick the smaller size
                let new_buffer_size = min(err_buffer_t.len_used, err_buffer_t.len_alloc) as usize;
                unsafe {
                    err_buffer.set_len(new_buffer_size);
                }
                // See https://gitlab.com/YottaDB/DB/YDB/-/issues/619
                debug_assert_ne!(status, YDB_ERR_TPRETRY);
                return Err(YDBError { message: err_buffer, status, tptoken });
            }
            break (ret_subs_used, subscripts);
        };
        assert!(
            ret_subs_used <= self.subscripts.len(),
            "growing the buffer should be handled in YDB_ERR_INSUFFSUBS (ydb {} > actual {})",
            ret_subs_used,
            self.subscripts.len()
        );
        self.subscripts.truncate(ret_subs_used);

        // Update the length of each subscript
        for (i, buff) in self.subscripts.iter_mut().enumerate() {
            let actual = buffer_structs[i].len_used as usize;
            unsafe {
                buff.set_len(actual);
            }
        }

        Ok(err_buffer)
    }

    /// Implements breadth-first traversal of a tree by searching for the next subscript.
    ///
    /// See also [KeyContext::next_sub](crate::context_api::KeyContext::next_sub).
    #[inline]
    pub(crate) fn sub_next_st(&self, tptoken: TpToken, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.direct_unsafe_call(tptoken, out_buffer, ydb_subscript_next_st)
    }

    /// Implements reverse breadth-first traversal of a tree by searching for the previous subscript.
    ///
    /// See also [KeyContext::prev_sub](crate::context_api::KeyContext::prev_sub).
    #[inline]
    pub(crate) fn sub_prev_st(&self, tptoken: TpToken, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.direct_unsafe_call(tptoken, out_buffer, ydb_subscript_previous_st)
    }

    // The Rust type system does not have a trait that means 'either a closure or an unsafe function'.
    // This function creates the appropriate closure for a call to `non_allocating_ret_call`.
    #[inline]
    fn direct_unsafe_call(
        &self, tptoken: TpToken, out_buffer: Vec<u8>,
        func: unsafe extern "C" fn(
            u64,
            *mut ydb_buffer_t,
            *const ydb_buffer_t,
            i32,
            *const ydb_buffer_t,
            *mut ydb_buffer_t,
        ) -> c_int,
    ) -> YDBResult<Vec<u8>> {
        let do_call = |tptoken, err_buffer_p, varname_p, len, subscripts_p, out_buffer_p| unsafe {
            func(tptoken, err_buffer_p, varname_p, len, subscripts_p, out_buffer_p)
        };
        self.non_allocating_ret_call(tptoken, out_buffer, do_call)
    }

    /// Implements breadth-first traversal of a tree by searching for the next subscript, and passes itself in as the output parameter.
    ///
    /// `sub_next_self_st` can be written (less efficiently) using only safe code; see the `sub_next_equivalent` test.
    ///
    /// See also [KeyContext::next_sub_self](crate::context_api::KeyContext::next_sub_self).
    pub(crate) fn sub_next_self_st(
        &mut self, tptoken: TpToken, out_buffer: Vec<u8>,
    ) -> YDBResult<Vec<u8>> {
        let next_subscript = self.sub_next_st(tptoken, out_buffer)?;
        // SAFETY: if there are no subscripts, `subscript_next` returns the next variable, which is always ASCII.
        Ok(unsafe { self.replace_last_buffer(next_subscript) })
    }

    /// Implements reverse breadth-first traversal of a tree by searching for the previous subscript, and passes itself in as the output parameter.
    ///
    /// `sub_prev_self_st` can be written (less efficiently) using only safe code; see the `sub_prev_equivalent` test.
    ///
    /// See also [KeyContext::prev_sub_self](crate::context_api::KeyContext::prev_sub_self).
    pub(crate) fn sub_prev_self_st(
        &mut self, tptoken: TpToken, out_buffer: Vec<u8>,
    ) -> YDBResult<Vec<u8>> {
        let next_subscript = self.sub_prev_st(tptoken, out_buffer)?;
        // SAFETY: if there are no subscripts, `subscript_prev` returns the next variable, which is always ASCII.
        Ok(unsafe { self.replace_last_buffer(next_subscript) })
    }

    /// Replace the last subscript of this node with `next_subscript`, or replace the variable if
    /// there are no subscripts.
    ///
    /// SAFETY: `next_subscript` must be valid UTF8 if there are no subscripts.
    unsafe fn replace_last_buffer(&mut self, next_subscript: Vec<u8>) -> Vec<u8> {
        let buffer = match self.last_mut() {
            Some(subscr) => subscr,
            None => self.variable.as_mut_vec(),
        };
        mem::replace(buffer, next_subscript)
    }

    fn make_out_buffer_t(out_buffer: &mut Vec<u8>) -> ydb_buffer_t {
        if out_buffer.capacity() == 0 {
            out_buffer.reserve(DEFAULT_CAPACITY);
        }

        ydb_buffer_t {
            buf_addr: out_buffer.as_mut_ptr() as *mut _,
            len_alloc: out_buffer.capacity() as u32,
            len_used: out_buffer.len() as u32,
        }
    }

    fn get_buffers_mut(&mut self) -> (ydb_buffer_t, Vec<ydb_buffer_t>) {
        let var = ydb_buffer_t {
            // `str::as_mut_ptr` was only stabilized in 1.36
            buf_addr: unsafe { self.variable.as_bytes_mut() }.as_mut_ptr() as *mut _,
            len_alloc: self.variable.capacity() as u32,
            len_used: self.variable.len() as u32,
        };
        let iter = self.subscripts.iter_mut();
        let subscripts = iter.map(Self::make_out_buffer_t).collect();
        (var, subscripts)
    }

    /// Same as get_buffers_mut but takes `&self`
    ///
    /// NOTE: The pointers returned in the `ConstYDBBuffer`s _must never be modified_.
    /// Doing so is immediate undefined behavior.
    /// This is why `ConstYDBBuffer` was created,
    /// so that modifying the private fields would be an error.
    fn get_buffers(&self) -> (ConstYDBBuffer, Vec<ConstYDBBuffer>) {
        let var = self.variable.as_bytes().into();
        let subscripts = self.subscripts.iter().map(|vec| vec.as_slice().into()).collect();
        (var, subscripts)
    }
}

#[repr(transparent)]
/// Because of this repr(transparent), it is safe to turn a
/// `*const ConstYDBBuffer` to `*const ydb_buffer_t`
struct ConstYDBBuffer<'a>(ydb_buffer_t, PhantomData<&'a [u8]>);

impl ConstYDBBuffer<'_> {
    fn as_ptr(&self) -> *const ydb_buffer_t {
        &self.0
    }
}

impl<'a> From<&'a [u8]> for ConstYDBBuffer<'a> {
    fn from(slice: &[u8]) -> Self {
        Self(
            ydb_buffer_t {
                buf_addr: slice.as_ptr() as *mut _,
                len_used: slice.len() as u32,
                len_alloc: slice.len() as u32,
            },
            PhantomData,
        )
    }
}

/// Allow Key to mostly be treated as a `Vec<Vec<u8>>` of subscripts,
/// but without `shrink_to_fit`, `drain`, or other methods that aren't relevant.
impl Key {
    /// Remove all subscripts after the `i`th index.
    ///
    /// # See also
    /// - [`Vec::truncate()`]
    pub fn truncate(&mut self, i: usize) {
        self.subscripts.truncate(i);
    }
    /// Remove all subscripts, leaving only the `variable`.
    ///
    /// # See also
    /// - [`Vec::clear()`]
    pub fn clear(&mut self) {
        self.subscripts.clear();
    }
    /// Add a new subscript, keeping all existing subscripts in place.
    ///
    /// # See also
    /// - [`Vec::push()`]
    pub fn push(&mut self, subscript: Vec<u8>) {
        self.subscripts.push(subscript);
    }
    /// Remove the last subscript, keeping all other subscripts in place.
    ///
    /// Note that this will _not_ return the `variable` even if there are no subscripts present.
    ///
    /// # See also
    /// - [`Vec::pop()`]
    pub fn pop(&mut self) -> Option<Vec<u8>> {
        self.subscripts.pop()
    }

    /// Returns a mutable pointer to the last subscript, or `None` if there are no subscripts.
    ///
    /// # See also
    /// - [`slice::last_mut()`](https://doc.rust-lang.org/std/primitive.slice.html#method.last_mut)
    pub fn last_mut(&mut self) -> Option<&mut Vec<u8>> {
        self.subscripts.last_mut()
    }
}

/// `Key` has all the *immutable* functions of a `Vec` of subscripts.
impl Deref for Key {
    type Target = Vec<Vec<u8>>;

    fn deref(&self) -> &Self::Target {
        &self.subscripts
    }
}

impl Index<usize> for Key {
    type Output = Vec<u8>;

    fn index(&self, i: usize) -> &Self::Output {
        &self.subscripts[i]
    }
}

impl IndexMut<usize> for Key {
    fn index_mut(&mut self, i: usize) -> &mut Vec<u8> {
        &mut self.subscripts[i]
    }
}

impl<S: Into<String>> From<S> for Key {
    fn from(s: S) -> Key {
        Key::variable(s)
    }
}

/// The status returned from a callback passed to [`Context::tp`]
///
/// [`Context::tp`]: crate::Context::tp
#[derive(Debug, Copy, Clone)]
pub enum TransactionStatus {
    /// Complete the transaction and commit all changes
    Ok = YDB_OK as isize,
    /// Undo changes specified in `locals_to_reset`, then restart the transaction
    Restart = YDB_TP_RESTART as isize,
    /// Abort the transaction and undo all changes
    Rollback = YDB_TP_ROLLBACK as isize,
}

type UserResult = Result<TransactionStatus, Box<dyn Error + Send + Sync>>;

#[derive(Debug)]
enum CallBackError {
    // the callback returned an error
    ApplicationError(Box<dyn Error + Send + Sync>),
    // the callback panicked; this is the value `panic!` was called with
    Panic(Box<dyn std::any::Any + Send + 'static>),
}
/// Passes the callback function as a structure to the callback
struct CallBackStruct<'a> {
    cb: &'a mut dyn FnMut(TpToken) -> UserResult,
    /// Application error (not a YDBError)
    error: Option<CallBackError>,
}

extern "C" fn fn_callback(tptoken: u64, _errstr: *mut ydb_buffer_t, tpfnparm: *mut c_void) -> i32 {
    // We can't tell if the pointer is invalid (unallocated or already freed) but we can check it's not null and aligned.
    // copied from https://github.com/rust-lang/rust/blob/84864bfea9c00fb90a1fa6e3af1d8ad52ce8f9ec/library/core/src/intrinsics.rs#L1742
    fn is_aligned_and_not_null<T>(ptr: *const T) -> bool {
        !ptr.is_null() && ptr as usize % std::mem::align_of::<T>() == 0
    }
    assert!(is_aligned_and_not_null(tpfnparm as *const CallBackStruct));
    let callback_struct = unsafe { &mut *(tpfnparm as *mut CallBackStruct) };

    let mut cb = panic::AssertUnwindSafe(&mut callback_struct.cb);
    let tptoken = TpToken(tptoken);
    // this deref_mut() is because Rust is having trouble with type inferrence
    let retval = match panic::catch_unwind(move || cb.deref_mut()(tptoken)) {
        Ok(val) => val,
        Err(payload) => {
            callback_struct.error = Some(CallBackError::Panic(payload));
            return YDB_TP_ROLLBACK;
        }
    };
    match retval {
        Ok(status) => status as i32,
        Err(err) => {
            // Try to cast into YDBError; if we can do that, return the error code
            // Else, rollback the transaction
            // FIXME: it's possible for a downstream user to wrap a YDBError in their own error,
            // in which case this may not return the right status.
            let status = if let Some(ydb_err) = err.downcast_ref::<YDBError>() {
                ydb_err.status
            } else {
                YDB_TP_ROLLBACK
            };
            callback_struct.error = Some(CallBackError::ApplicationError(err));
            status
        }
    }
}

/// Start a new transaction, where `f` is the transaction to execute.
///
/// See also [Context::tp](crate::context_api::KeyContext::tp).
pub(crate) fn tp_st<F>(
    tptoken: TpToken, mut err_buffer: Vec<u8>, mut f: F, trans_id: &str, locals_to_reset: &[&str],
) -> Result<Vec<u8>, Box<dyn Error + Send + Sync>>
where
    F: FnMut(TpToken) -> UserResult,
{
    let mut err_buffer_t = Key::make_out_buffer_t(&mut err_buffer);

    let mut locals: Vec<ConstYDBBuffer> = Vec::with_capacity(locals_to_reset.len());
    for &local in locals_to_reset.iter() {
        locals.push(local.as_bytes().into());
    }
    let locals_ptr = match locals.len() {
        0 => ptr::null(),
        _ => locals.as_ptr(),
    };
    let c_str = CString::new(trans_id).unwrap();
    let mut callback_struct = CallBackStruct { cb: &mut f, error: None };
    let arg = &mut callback_struct as *mut _ as *mut c_void;
    let status = unsafe {
        ydb_tp_st(
            tptoken.into(),
            &mut err_buffer_t,
            Some(fn_callback),
            arg,
            c_str.as_ptr(),
            locals.len() as i32,
            locals_ptr as *const _,
        )
    };
    if status as u32 == YDB_OK {
        // there may be a possibility for an error to occur that gets caught
        // and handled which appear to use the buffer even though none was
        // returned at a high level.
        unsafe {
            err_buffer.set_len(min(err_buffer_t.len_used, err_buffer_t.len_alloc) as usize);
        }
        Ok(err_buffer)
    } else if let Some(user_err) = callback_struct.error {
        match user_err {
            // an application error occurred; we _could_ return out_buffer if the types didn't conflict below
            CallBackError::ApplicationError(mut err) => {
                if let Some(ydb_err) = err.downcast_mut::<YDBError>() {
                    // Use the outer tptoken, not the inner one. The inner transaction has already ended.
                    ydb_err.tptoken = tptoken;
                }
                Err(err)
            }
            // reraise the panic now that we're past the FFI barrier
            CallBackError::Panic(payload) => panic::resume_unwind(payload),
        }
    } else {
        // a YDB error occurred; reuse out_buffer to return an error
        unsafe {
            err_buffer.set_len(min(err_buffer_t.len_used, err_buffer_t.len_alloc) as usize);
        }
        // See https://gitlab.com/YottaDB/DB/YDB/-/issues/619
        debug_assert_ne!(status, YDB_ERR_TPRETRY);
        Err(Box::new(YDBError { message: err_buffer, status, tptoken }))
    }
}

/// Delete all local variables _except_ for those passed in `saved_variable`.
///
/// See also [Context::delete_excl](crate::context_api::Context::delete_excl).
pub(crate) fn delete_excl_st(
    tptoken: TpToken, err_buffer: Vec<u8>, saved_variables: &[&str],
) -> YDBResult<Vec<u8>> {
    use crate::craw::ydb_delete_excl_st;

    let varnames: Vec<ConstYDBBuffer> =
        saved_variables.iter().map(|var| var.as_bytes().into()).collect();

    resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| unsafe {
        ydb_delete_excl_st(
            tptoken,
            err_buffer_p,
            varnames.len() as c_int,
            varnames.as_ptr() as *const _,
        )
    })
}

/// Given a binary sequence, serialize it to 'Zwrite format', which is ASCII printable.
///
/// See also [Context::str2zwr](crate::context_api::Context::str2zwr).
pub(crate) fn str2zwr_st(
    tptoken: TpToken, out_buf: Vec<u8>, original: &[u8],
) -> YDBResult<Vec<u8>> {
    use crate::craw::ydb_str2zwr_st;

    let original_t = ConstYDBBuffer::from(original);
    resize_ret_call(tptoken, out_buf, |tptoken, err_buffer_p, out_buffer_p| unsafe {
        ydb_str2zwr_st(tptoken, err_buffer_p, original_t.as_ptr(), out_buffer_p)
    })
}

/// Given a buffer in 'Zwrite format', deserialize it to the original binary buffer.
///
/// See also [Context::zwr2str](crate::context_api::Context::zwr2str).
pub(crate) fn zwr2str_st(
    tptoken: TpToken, out_buf: Vec<u8>, serialized: &[u8],
) -> Result<Vec<u8>, YDBError> {
    use crate::craw::ydb_zwr2str_st;

    let serialized_t = ConstYDBBuffer::from(serialized);
    resize_ret_call(tptoken, out_buf, |tptoken, err_buffer_p, out_buffer_p| unsafe {
        ydb_zwr2str_st(tptoken, err_buffer_p, serialized_t.as_ptr(), out_buffer_p)
    })
}

/// Write the message corresponding to a YottaDB error code to `out_buffer`.
///
/// See also [Context::message](crate::context_api::Context::message).
pub(crate) fn message_t(tptoken: TpToken, out_buffer: Vec<u8>, status: i32) -> YDBResult<Vec<u8>> {
    resize_ret_call(tptoken, out_buffer, |tptoken, err_buffer_p, out_buffer_p| unsafe {
        ydb_message_t(tptoken, err_buffer_p, status, out_buffer_p)
    })
}

/// Return a string in the format `rustwr <rust wrapper version> <$ZYRELEASE>`
///
/// See also [Context::release](crate::context_api::Context::release).
pub(crate) fn release_t(tptoken: TpToken, out_buffer: Vec<u8>) -> YDBResult<String> {
    let zrelease = Key::variable("$ZYRELEASE").get_st(tptoken, out_buffer)?;
    let zrelease = String::from_utf8(zrelease).expect("$ZRELEASE was not valid UTF8");
    Ok(format!("rustwr {} {}", env!("CARGO_PKG_VERSION"), zrelease))
}

/// Runs the YottaDB deferred signal handler (if necessary).
///
/// See also [Context::eintr_handler](crate::context_api::Context::eintr_handler).
pub(crate) fn eintr_handler_t(tptoken: TpToken, err_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
    use crate::craw::ydb_eintr_handler_t;

    resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| unsafe {
        ydb_eintr_handler_t(tptoken, err_buffer_p)
    })
}

/// Acquires locks specified in `locks` and releases all others.
///
/// See also [Context::lock](crate::context_api::Context::lock).
#[cfg(any(target_pointer_width = "64", target_pointer_width = "32"))]
pub(crate) fn lock_st(
    tptoken: TpToken, mut out_buffer: Vec<u8>, timeout: Duration, locks: &[Key],
) -> YDBResult<Vec<u8>> {
    use std::convert::TryFrom;
    use crate::craw::{
        YDB_ERR_MAXARGCNT, YDB_ERR_TIME2LONG, MAX_GPARAM_LIST_ARGS, ydb_lock_st,
        ydb_call_variadic_plist_func, gparam_list,
    };
    // `ydb_lock_st` is hard to work with because it uses variadic arguments.
    // The only way to pass a variable number of arguments in Rust is to pass a slice
    // or use a macro (i.e. know the number of arguments ahead of time).

    // To get around this, `lock_st` calls the undocumented `ydb_call_variadic_plist_func` function.
    // `ydb_call_variadic_plist_func` takes the function to call, and a { len, args } struct.
    // `args` is a pointer to an array of length at most MAX_GPARAM_LIST_ARGS.
    // Under the covers, this effectively reimplements a user-land `va_list`,
    // turning a function that takes explicit number of parameters of a known type (`ydb_call_variadic_plist_func`)
    // into a variadic function call (`ydb_lock_st`).

    // Each `arg` is typed as being a `void *`,
    // which means that on 32-bit platforms, 64-bit arguments have to be passed as 2 separate arguments.
    // This will hopefully be changed in YDB r1.32 to take a `uint64_t` instead.

    // The function passed to `ydb_call_variadic_plist_func`
    // is typed as taking the number of arguments and then a variable number of args.
    // This is incorrect; any function can be passed to `ydb_call_variadic_plist_func`
    // as long as the parameters it takes match the arguments passed.
    // This is not planned to change in the near future.

    let mut err_buffer_t = Key::make_out_buffer_t(&mut out_buffer);
    let keys: Vec<_> = locks.iter().map(|k| k.get_buffers()).collect();

    type Void = *mut c_void;
    // Setup the initial args.
    // Note that all these arguments are required to have size of `void*`,
    // whatever that is on the target.
    let mut arg = [0 as Void; MAX_GPARAM_LIST_ARGS as usize];
    let mut i: usize;

    // we can't just use `as usize` since on 32-bit platforms that will discard the upper half of the value
    // NOTE: this could be wrong if the pointer width is different from `usize`. We don't handle this case.
    let timeout_ns = match u64::try_from(timeout.as_nanos()) {
        Ok(n) => n,
        Err(_) => {
            // discard any previous error
            out_buffer.clear();
            return Err(YDBError { status: YDB_ERR_TIME2LONG, message: out_buffer, tptoken });
        }
    };
    #[cfg(target_pointer_width = "64")]
    {
        arg[0] = tptoken.0 as Void;
        arg[1] = &mut err_buffer_t as *mut _ as Void;
        arg[2] = timeout_ns as Void;
        arg[3] = keys.len() as Void;
        i = 4;
    }
    #[cfg(target_pointer_width = "32")]
    {
        let tptoken = tptoken.0;
        #[cfg(target_endian = "little")]
        {
            arg[0] = (tptoken & 0xffffffff) as Void;
            arg[1] = (tptoken >> 32) as Void;
            // arg[2] is err_buffer_t, but we need to use 2 slots for it to avoid unaligned accesses :(
            // here's hoping that YDB gets a better API upstream soon ...
            arg[4] = (timeout_ns & 0xffffffff) as Void;
            arg[5] = (timeout_ns >> 32) as Void;
        }
        #[cfg(target_endian = "big")]
        {
            let LOCK_ST_IS_UNTESTED_AND_UNSUPPORTED_ON_THIS_PLATFORM = ();
            arg[0] = (tptoken >> 32) as Void;
            arg[1] = (tptoken & 0xffffffff) as Void;
            arg[4] = (timeout_ns >> 32) as Void;
            arg[5] = (timeout_ns & 0xffffffff) as Void;
        }
        arg[2] = &mut err_buffer_t as *mut _ as Void;
        arg[6] = keys.len() as Void;
        i = 7;
    }

    for (var, subscripts) in keys.iter() {
        if i + 2 >= MAX_GPARAM_LIST_ARGS as usize {
            return Err(YDBError {
                status: YDB_ERR_MAXARGCNT,
                message: format!("Expected at most {} arguments, got {}", MAX_GPARAM_LIST_ARGS, i)
                    .into_bytes(),
                tptoken,
            });
        }
        // we've already used some of the slots for the initial parameters,
        // so just keep a manual count instead of `enumerate`.
        arg[i] = var.as_ptr() as Void;
        arg[i + 1] = subscripts.len() as Void;
        arg[i + 2] = subscripts.as_ptr() as Void;
        i += 3;
    }

    // In C, all pointers are mutable by default `const` is specified. Accordingly, `args` is
    // declared as mutable here, since it will be passed to C as the `cvplist` argument of
    // `ydb_call_variadic_plist_func()`, which is not declared as `const`.
    let mut args = gparam_list { n: i as isize, arg };
    let status = unsafe {
        // The types on `ydb_call_variadic_plist_func` are not correct. That is, `ydb_vplist_func` is defined as
        //      `typedef	uintptr_t	(*ydb_vplist_func)(uintptr_t cnt, ...)`,
        // but the type signature for `ydb_lock_st` is
        //      `int	ydb_lock_st(uint64_t tptoken, ydb_buffer_t *errstr, unsigned long long timeout_nsec, int namecount, ...);`.
        //
        // Additionally, `ydb_lock_st` on its own is a unique zero-sized-type (ZST):
        // See https://doc.rust-lang.org/reference/types/function-item.html#function-item-types for more details on function types
        // and https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts for details on ZSTs.
        // This `as *const ()` turns the unique ZST for `ydb_lock_st` into a proper function pointer.
        // Without the `as` cast, `transmute` will return `1_usize` and `ydb_call` will subsequently segfault.
        let ydb_lock_as_vplist_func = std::mem::transmute(ydb_lock_st as *const ());
        ydb_call_variadic_plist_func(Some(ydb_lock_as_vplist_func), &mut args as *mut gparam_list)
    };

    // We could end up with a buffer of a larger size if we couldn't fit the error string
    // into the out_buffer, so make sure to pick the smaller size
    let len = min(err_buffer_t.len_used, err_buffer_t.len_alloc) as usize;
    unsafe {
        out_buffer.set_len(len);
    }

    if status != YDB_OK as c_int {
        debug_assert_ne!(status, YDB_ERR_TPRETRY);
        Err(YDBError { message: out_buffer, status, tptoken })
    } else {
        Ok(out_buffer)
    }
}

/// A call to the YDB API which only needs an `err_buffer`, not an `out_buffer`.
///
/// See documentation for [`non_allocating_call`] for more details.
///
/// `F: FnMut(tptoken, out_buffer_t) -> status`
#[doc(hidden)] // public for `ci_t!`
pub fn resize_call<F>(tptoken: TpToken, err_buffer: Vec<u8>, mut func: F) -> YDBResult<Vec<u8>>
where
    F: FnMut(u64, *mut ydb_buffer_t) -> c_int,
{
    resize_ret_call(tptoken, err_buffer, |tptoken, err_buffer_p, out_buffer_p| {
        let status = func(tptoken, err_buffer_p);
        unsafe {
            (*out_buffer_p).len_used = (*err_buffer_p).len_used;
        }
        status
    })
}

/// A call to the YDB API which could need either an `err_buffer` or an `out_buffer`, but not both at once.
/// This uses the same underlying allocation (in `out_buffer`) for both.
///
/// See documentation for `non_allocating_ret_call` for more details.
///
/// `F: FnMut(tptoken, err_buffer_t, out_buffer_t) -> status`
fn resize_ret_call<F>(tptoken: TpToken, mut out_buffer: Vec<u8>, mut func: F) -> YDBResult<Vec<u8>>
where
    F: FnMut(u64, *mut ydb_buffer_t, *mut ydb_buffer_t) -> c_int,
{
    #[cfg(debug_assertions)]
    let mut i = 0;

    let status = loop {
        let mut out_buffer_t = Key::make_out_buffer_t(&mut out_buffer);
        // NOTE: it is very important that this makes a copy of `out_buffer_t`:
        // otherwise, on `INVSTRLEN`, when YDB tries to set len_used it will overwrite the necessary
        // capacity with the length of the string.
        let mut err_buffer_t = out_buffer_t;
        // Do the call
        let status = func(tptoken.into(), &mut err_buffer_t, &mut out_buffer_t);
        // Handle resizing the buffer, if needed
        // The goal here is to catch any `INVSTRLEN` errors and resize the `out_buffer` to be large enough,
        // rather than forcing the end user to do it themselves.
        // However, in some edge cases, it's possible the `INVSTRLEN` will refer _not_ to `out_buffer`,
        // but to some other buffer that `func` passed in inside a nested call.
        // In particular, M FFI calls using `ci_t!` could accept ydb_string_t return types but not have enough memory allocated.
        // But there's no way to tell whether this is a call from `ci_t!` or not.
        // The trick this uses is to see if the existing `capacity` is already as long as `len_used`:
        // If so, the `INVSTRLEN` must be referring to a different buffer and there's nothing we can do about it.
        if status == YDB_ERR_INVSTRLEN {
            let len = out_buffer_t.len_used as usize;
            if out_buffer.capacity() >= len {
                return Err(YDBError { tptoken, message: out_buffer, status });
            }
            out_buffer.resize(len, 0);
            #[cfg(debug_assertions)]
            {
                i += 1;
                assert!(i <= 10, "possible infinite loop in `resize_ret_call`");
            }
            continue;
        }
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        let len = if status != YDB_OK as i32 {
            min(err_buffer_t.len_used, err_buffer_t.len_alloc)
        } else {
            min(out_buffer_t.len_used, out_buffer_t.len_alloc)
        };
        unsafe {
            out_buffer.set_len(len as usize);
        }
        break status;
    };
    if status != YDB_OK as i32 {
        debug_assert_ne!(status, YDB_ERR_TPRETRY);
        Err(YDBError { tptoken, message: out_buffer, status })
    } else {
        Ok(out_buffer)
    }
}

#[cfg(test)]
pub(crate) mod tests;

// Used for `compile_fail` tests
#[doc(hidden)]
#[cfg(doctest)]
/// Tests that `YDBError` cannot be constructed outside the `yottadb` crate.
/// ```compile_fail
/// use yottadb::*;
/// use yottadb::craw::YDB_OK;
/// let ydb_err = YDBError {
///   tptoken: YDB_NOTTP,
///   message: Vec::new(),
///   status: 0,
/// };
/// ```
pub fn used_for_doctests() {}
