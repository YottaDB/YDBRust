/****************************************************************
*                                                               *
* Copyright (c) 2019-2020 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

//! Provides a more-friendly Rust-interface to the YottaDB API than the
//! raw C API (craw).
//!
//! Most operations are encapsulated in methods on the [`Key`][key] struct, and generally
//! consume a Vec<u8> and return [`YDBResult<Vec<u8>>`][YDBResult]. The return Vec<u8> will either contain
//! the data fetched from the database or an error.
//!
//! The Vec<u8> may be resized as part of the call.
//!
//! # Intrinsic Variables
//!
//! YottaDB has several intrinsic variables which are documented [online][intrinsics].
//! To get the value of these variables, call `get_st` on a `Key` with the name of the variable.
//!
//! # Examples
//!
//! A basic database operation (set a value, retrieve it, then delete it):
//!
//! ```
//! use yottadb::{YDB_NOTTP, DeleteType, YDBResult};
//! use yottadb::simple_api::Key;
//!
//! fn main() -> YDBResult<()> {
//!     let mut key = yottadb::make_key!("^MyGlobal", "SubscriptA", "42");
//!     let mut buffer = Vec::with_capacity(1024);
//!     let value = "This is a persistent message";
//!     buffer = key.set_st(YDB_NOTTP, buffer, value)?;
//!     buffer = key.get_st(YDB_NOTTP, buffer)?;
//!     assert_eq!(&buffer, b"This is a persistent message");
//!     key.delete_st(YDB_NOTTP, buffer, DeleteType::DelNode).unwrap();
//!     Ok(())
//! }
//! ```
//!
//! Get the instrinsic variable [`$tlevel`][tlevel], which gives the current transaction level.
//!
//! ```
//! use yottadb::{YDB_NOTTP, YDBResult};
//!
//! fn main() -> YDBResult<()> {
//!     let mut key = yottadb::make_key!("$tlevel");
//!     let buffer = Vec::with_capacity(10);
//!     let buffer = key.get_st(YDB_NOTTP, buffer)?;
//!     let tlevel: usize = String::from_utf8_lossy(&buffer).parse()
//!         .expect("$tlevel should be an integer");
//!     assert_eq!(tlevel, 0_usize);
//!     Ok(())
//! }
//! ```
//!
//! [key]: struct.Key.html
//! [intrinsics]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#intrinsic-special-variables
//! [tlevel]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#tlevel
//! [YDBResult]: type.YDBResult.html

pub mod call_in;

use std::error::Error;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::ptr;
use std::ffi::CString;
use std::os::raw::{c_void, c_int};
use std::time::Duration;
use std::cmp::min;
use std::fmt;
use std::error;
use std::panic;
use crate::craw::{
    ydb_buffer_t, ydb_get_st, ydb_set_st, ydb_data_st, ydb_delete_st, ydb_message_t, ydb_incr_st,
    ydb_node_next_st, ydb_node_previous_st, ydb_subscript_next_st, ydb_subscript_previous_st,
    ydb_tp_st, YDB_OK, YDB_ERR_INVSTRLEN, YDB_ERR_INSUFFSUBS, YDB_DEL_TREE, YDB_DEL_NODE,
    YDB_TP_RESTART, YDB_TP_ROLLBACK,
};

const DEFAULT_CAPACITY: usize = 50;

/// An error returned by the underlying YottaDB library.
///
/// This error should not be constructed manually.
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
    pub tptoken: TpToken,
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

impl error::Error for YDBError {
    fn cause(&self) -> Option<&dyn error::Error> {
        Some(self)
    }
}

/// A specialized `Result` type returned by a YottaDB function.
pub type YDBResult<T> = Result<T, YDBError>;

/// A transaction processing token, used by yottadb to ensure ACID properties.
///
/// The only valid values for a TpToken are the default (`TpToken::default()`)
/// or a token passed in from [`tp_st`](fn.tp_st.html).
///
/// TpTokens can be converted to `u64`, but not vice-versa.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub struct TpToken(pub(crate) u64);

impl Default for TpToken {
    fn default() -> Self {
        TpToken(crate::craw::YDB_NOTTP)
    }
}

impl Into<u64> for TpToken {
    fn into(self) -> u64 {
        self.0
    }
}

/// The type of data available at the current node.
///
/// # See also
/// - [`Key::data_st()`](struct.Key.html#method.data_st)
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
/// - [`Key::delete_st()`](struct.Key.html#method.delete_st)
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum DeleteType {
    /// Delete only this node.
    DelNode,
    /// Delete this node and all subnodes in the tree.
    DelTree,
}

/// Provides a [`Key`][key] object for the given subscripts.
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
/// [key]: simple_api/struct.Key.html
/// [nodes-and-variables]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#keys-values-nodes-variables-and-subscripts
#[macro_export]
macro_rules! make_key {
    ( $var:expr $(,)? ) => (
        $crate::simple_api::Key::variable($var)
    );
    ( $var: expr $( , $subscript: expr)+ $(,)? ) => (
        $crate::simple_api::Key::new($var, &[
            $($subscript),*
        ])
    );
}

/// A key used to get, set, and delete values in the database.
///
/// # See also
/// - [`KeyContext`](../context_api/struct.KeyContext.html)
/// - [Keys, values, nodes, variables, and subscripts](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#keys-values-nodes-variables-and-subscripts)
/// - [Local and Global variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#local-and-global-variables)
/// - [Intrinsic special variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#intrinsic-special-variables)
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct Key {
    /// The [variable] of the key, which can be freely modified.
    ///
    /// Note that not all variables are valid.
    /// If a `variable` is set to an invalid value, the next call to YottaDB
    /// will result in a [`YDB_ERR_INVVARNAME`](../craw/constant.YDB_ERR_INVVARNAME.html).
    /// See [variables vs. subscripts][variable] for details on what variables are valid and invalid.
    ///
    /// [variable]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#variables-vs-subscripts-vs-values
    pub variable: String,
    subscripts: Vec<Vec<u8>>,
}

impl Key {
    /// Create a new key.
    ///
    /// Note that not all variables are valid.
    /// See the [upstream documentation][vars] for information on valid variables.
    /// `Key::new()` will not currently give an error for invalid variables,
    /// but any operation using them will return a YDBError(%YDB-E-INVVARNAME).
    ///
    /// # Examples
    ///
    /// Creating a variable from string subscripts is simple:
    ///
    /// ```rust
    /// use yottadb::simple_api::Key;
    /// Key::new("hello", &["good morning", "good evening"]);
    /// ```
    ///
    /// Creating a variable with no subscripts is a little more complicated.
    /// Consider using `Key::variable` instead.
    ///
    /// ```
    /// # use yottadb::simple_api::Key;
    /// Key::new::<_, Vec<_>>("hello", &[]);
    /// ```
    ///
    /// For implementation reasons, creating a new key with bytestrings is
    /// syntactically tricky.
    ///
    /// ```compile_fail
    /// # use yottadb::simple_api::Key;
    /// // does not work: `From<[u8; 2]> is not implemented for Vec<u8>`
    /// Key::new("hello", &[b"hi"]);
    /// ```
    ///
    /// Here is the proper syntax:
    ///
    /// ```
    /// # use yottadb::simple_api::Key;
    /// Key::new("hello", &[&b"hi"[..]]);
    /// ```
    ///
    /// This has been [fixed on nightly][from-arr-issue] and will land on stable on [June 4th][release-date].
    ///
    /// [vars]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#variables-vs-subscripts-vs-values
    /// [from-arr-issue]: https://github.com/rust-lang/rust/issues/67963
    /// [release-date]: https://forge.rust-lang.org/#current-release-versions
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
    /// Shortcut for creating a key with no subscripts.
    pub fn variable<V: Into<String>>(var: V) -> Key {
        Key::new::<V, Vec<u8>>(var, &[])
    }
    /// Gets the value of this key from the database and returns the value.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_GVUNDEF, YDB_ERR_INVSVN, YDB_ERR_LVUNDEF as appropriate if no such variable or node exists
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^hello");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, "Hello world!")?;
    ///     output_buffer = key.get_st(TpToken::default(), output_buffer)?;
    ///
    ///     assert_eq!(&output_buffer, b"Hello world!");
    ///
    ///     Ok(())
    /// }
    /// ```
    #[inline]
    pub fn get_st(&self, tptoken: TpToken, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.direct_unsafe_call(tptoken, out_buffer, ydb_get_st)
    }

    /// Sets the value of a key in the database.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_INVSVN if no such intrinsic special variable exists
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^hello");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     key.set_st(TpToken::default(), output_buffer, b"Hello world!")?;
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn set_st<U>(&self, tptoken: TpToken, err_buffer: Vec<u8>, new_val: U) -> YDBResult<Vec<u8>>
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

    /// Retuns the following information in DataReturn about a local or global variable node:
    ///
    /// - NoData: There is neither a value nor a subtree; i.e it is undefined.
    /// - ValueData: There is a value, but no subtree.
    /// - TreeData: There is no value, but there is a subtree.
    /// - ValueTreeData: There are both a value and a subtree.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - [error return
    /// codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult, DataReturn};
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^helloValueDoesntExist");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     let (output, output_buffer) = key.data_st(TpToken::default(), output_buffer)?;
    ///
    ///     assert_eq!(DataReturn::NoData, output);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn data_st(
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
    /// A value of DelNode or DelTree for DeleteType specifies whether to delete just the node at the root, leaving the (sub)tree intact, or to delete the node as well as the (sub)tree.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult, DeleteType};
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^hello");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.delete_st(TpToken::default(), output_buffer, DeleteType::DelTree)?;
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn delete_st(
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

    /// Converts the value to a number and increments it based on the value specifed by Option.
    /// It defaults to 1 if the value is NULL.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NUMOFLOW
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # See also
    ///
    /// - [How YDB stores numbers internally](https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#numeric-considerations)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let mut key = make_key!("^helloIncrementDocTest");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, "0")?;
    ///     output_buffer = key.get_st(TpToken::default(), output_buffer)?;
    ///     let before: i32 = String::from_utf8_lossy(&output_buffer).parse()?;
    ///     output_buffer = key.incr_st(TpToken::default(), output_buffer, None)?;
    ///     let now: i32  = String::from_utf8_lossy(&output_buffer).parse()?;
    ///     output_buffer = key.get_st(TpToken::default(), output_buffer)?;
    ///     let after: i32 = String::from_utf8_lossy(&output_buffer).parse()?;
    ///
    ///     assert!(before < now);
    ///     assert!(before + 1 == now);
    ///     assert!(after == now);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn incr_st(
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
    /// When a lock goes from 1 to 0, it is released.
    /// Attempting to decrement a lock not owned by the current process has no effect.
    ///
    /// # Errors
    /// - `YDB_ERR_INVVARNAME` if `self.variable` is not a valid variable name.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), yottadb::YDBError> {
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::Key;
    /// use std::time::Duration;
    ///
    /// let key = Key::variable("lockDecrStTest");
    /// key.lock_incr_st(TpToken::default(), Vec::new(), Duration::from_secs(1))?;
    /// key.lock_decr_st(TpToken::default(), Vec::new())?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # See also
    /// - The C [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-lock-decr-s-ydb-lock-decr-st)
    /// - [Locks](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#locks)
    /// - [Variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#variables-vs-subscripts-vs-values)
    #[inline]
    pub fn lock_decr_st(&self, tptoken: TpToken, err_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        use crate::craw::ydb_lock_decr_st;
        let do_call = |tptoken, err_buffer_p, varname_p, len, subscripts_p| unsafe {
            ydb_lock_decr_st(tptoken, err_buffer_p, varname_p, len, subscripts_p)
        };
        self.non_allocating_call(tptoken, err_buffer, do_call)
    }
    /// Increment the count of a lock held by the process, or acquire a new lock.
    ///
    /// If the lock is not currently held by this process, it is acquired.
    /// Otherwise, the lock count is incremented.
    ///
    /// `timeout` specifies a time that the function waits to acquire the requested locks.
    /// If `timeout` is 0, the function makes exactly one attempt to acquire the lock.
    ///
    /// # Errors
    /// - `YDB_ERR_INVVARNAME` if `self.variable` is not a valid variable name.
    /// - `YDB_LOCK_TIMEOUT` if the lock could not be acquired within the specific time.
    /// - `YDB_ERR_TIME2LONG` if `timeout.as_nanos()` exceeds `YDB_MAX_TIME_NSEC`
    ///                    or if `timeout.as_nanos()` does not fit into a `c_ulonglong`.
    /// - Another [error code](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), yottadb::YDBError> {
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::Key;
    /// use std::time::Duration;
    ///
    /// let key = Key::variable("lockIncrStTest");
    /// key.lock_incr_st(TpToken::default(), Vec::new(), Duration::from_secs(1))?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # See also
    /// - The C [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-lock-decr-s-ydb-lock-decr-st)
    /// - [Locks](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#locks)
    /// - [Variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#variables-vs-subscripts-vs-values)
    pub fn lock_incr_st(
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
    /// For more information on variable trees, see the [overview of YottaDB][how-it-works]
    /// as well as the section on [variables and nodes][vars-nodes].
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloNodeNextSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, "Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, "Hello")?;
    ///     // Lose the subscript, or pretend we are starting at ""
    ///     key[0].clear();
    ///     output_buffer = key.node_next_self_st(TpToken::default(), output_buffer)?;
    ///
    ///     assert_eq!(&key[0], b"a");
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// [how-it-works]: https://yottadb.com/product/how-it-works/
    /// [vars-nodes]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#keys-values-nodes-variables-and-subscripts
    #[inline]
    pub fn node_next_self_st(
        &mut self, tptoken: TpToken, out_buffer: Vec<u8>,
    ) -> YDBResult<Vec<u8>> {
        self.growing_shrinking_call(tptoken, out_buffer, ydb_node_next_st)
    }

    /// Facilitates reverse depth-first traversal of a local or global variable tree and reports the predecessor node, passing itself in as the output parameter.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND.
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloNodePrevSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, "Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, "Hello")?;
    ///     // We need to start at node beyond the node we are looking for; just add some Z's
    ///     key[0] = Vec::from("z");
    ///     output_buffer = key.node_prev_self_st(TpToken::default(), output_buffer)?;
    ///
    ///     assert_eq!(key[0], b"b");
    ///
    ///     Ok(())
    /// }
    /// ```
    #[inline]
    pub fn node_prev_self_st(
        &mut self, tptoken: TpToken, out_buffer: Vec<u8>,
    ) -> YDBResult<Vec<u8>> {
        self.growing_shrinking_call(tptoken, out_buffer, ydb_node_previous_st)
    }

    fn growing_shrinking_call(
        &mut self, tptoken: TpToken, mut err_buffer: Vec<u8>,
        c_func: unsafe extern "C" fn(
            u64,
            *mut ydb_buffer_t,
            *const ydb_buffer_t,
            c_int,
            *const ydb_buffer_t,
            *mut c_int,
            *mut ydb_buffer_t,
        ) -> c_int,
    ) -> YDBResult<Vec<u8>> {
        let len = self.subscripts.len() as i32;
        let mut err_buffer_t = Self::make_out_buffer_t(&mut err_buffer);

        // this is a loop instead of a recursive call so we can keep the original `len`
        let (ret_subs_used, buffer_structs) = loop {
            // Make sure `subscripts` is not a null pointer
            if self.subscripts.is_empty() {
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
                    len,
                    subscripts.as_ptr(),
                    &mut ret_subs_used as *mut _,
                    subscripts.as_mut_ptr(),
                )
            };
            let ret_subs_used = ret_subs_used as usize;
            // Handle resizing the buffer, if needed
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
            if status == crate::craw::YDB_ERR_PARAMINVALID {
                let i = ret_subs_used;
                panic!(
                    "internal error in node_prev_st: subscripts[{}] was null: {:?}",
                    i, subscripts[i]
                );
            }
            // Set length of the vec containing the buffer to we can see the value
            if status != YDB_OK as i32 {
                // We could end up with a buffer of a larger size if we couldn't fit the error string
                // into the out_buffer buffer, so make sure to pick the smaller size
                let new_buffer_size = min(err_buffer_t.len_used, err_buffer_t.len_alloc) as usize;
                unsafe {
                    err_buffer.set_len(new_buffer_size);
                }
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
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let mut key = make_key!("^helloSubNext", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, b"Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, b"Hello")?;
    ///     // Start at a, next subscript will be b
    ///     key[0] = Vec::from("a");
    ///     output_buffer = key.sub_next_st(TpToken::default(), output_buffer)?;
    ///
    ///     assert_eq!(&output_buffer, b"b");
    ///
    ///     Ok(())
    /// }
    /// ```
    #[inline]
    pub fn sub_next_st(&self, tptoken: TpToken, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.direct_unsafe_call(tptoken, out_buffer, ydb_subscript_next_st)
    }

    /// Implements reverse breadth-first traversal of a tree by searching for the previous subscript.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let mut key = make_key!("^helloSubPrev", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, b"Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, b"Hello")?;
    ///     // Starting at b, the previous subscript should be a
    ///     output_buffer = key.sub_prev_st(TpToken::default(), output_buffer)?;
    ///
    ///     assert_eq!(&output_buffer, b"a");
    ///
    ///     Ok(())
    /// }
    /// ```
    #[inline]
    pub fn sub_prev_st(&self, tptoken: TpToken, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
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
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^helloSubNextSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, b"Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, b"Hello")?;
    ///     // Starting at a, the next sub should be b
    ///     key[0] = Vec::from("a");
    ///     output_buffer = key.sub_next_self_st(TpToken::default(), output_buffer)?;
    ///
    ///     assert_eq!(&key[0], b"b");
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// `sub_next_self_st` can be written (less efficiently) using only safe code:
    /// ```
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// # fn main() -> YDBResult<()> {
    ///
    /// // set up a node with data at `subNextSelfUser("b")`
    /// let mut user = Key::new("subNextSelfUser", &["b"]);
    /// user.set_st(TpToken::default(), Vec::new(), b"Hello")?;
    ///
    /// user[0] = "a".into();
    /// user[0] = user.sub_next_st(TpToken::default(), Vec::new())?;
    ///
    /// let mut ydb = Key::new("subNextSelfUser", &["a"]);
    /// ydb.sub_next_self_st(TpToken::default(), Vec::new())?;
    ///
    /// assert_eq!(user[0], ydb[0]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn sub_next_self_st(
        &mut self, tptoken: TpToken, out_buffer: Vec<u8>,
    ) -> YDBResult<Vec<u8>> {
        self.sub_self_call(tptoken, out_buffer, ydb_subscript_next_st)
    }

    /// Implements reverse breadth-first traversal of a tree by searching for the previous subscript, and passes itself in as the output parameter.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^helloSubPrevSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, b"Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(TpToken::default(), output_buffer, b"Hello")?;
    ///     // Starting at b, previous should be a
    ///     output_buffer = key.sub_prev_self_st(TpToken::default(), output_buffer)?;
    ///
    ///     assert_eq!(&key[0], b"a");
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// `sub_prev_self_st` can be written (less efficiently) using only safe code:
    /// ```
    /// use yottadb::TpToken;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// # fn main() -> YDBResult<()> {
    ///
    /// // set up a node with data at `subPrevSelfUser("a")`
    /// let mut user = Key::new("subPrevSelfUser", &["a"]);
    /// user.set_st(TpToken::default(), Vec::new(), b"Hello")?;
    ///
    /// user[0] = "b".into();
    /// user[0] = user.sub_prev_st(TpToken::default(), Vec::new()).unwrap();
    ///
    /// let mut ydb = Key::new("subPrevSelfUser", &["b"]);
    /// ydb.sub_prev_self_st(TpToken::default(), Vec::new())?;
    ///
    /// assert_eq!(user[0], ydb[0]);
    /// # Ok(())
    /// # }
    pub fn sub_prev_self_st(
        &mut self, tptoken: TpToken, out_buffer: Vec<u8>,
    ) -> YDBResult<Vec<u8>> {
        self.sub_self_call(tptoken, out_buffer, ydb_subscript_previous_st)
    }

    // `sub_prev_self` and `sub_next_self` use the same memory allocation logic.
    fn sub_self_call(
        &mut self, tptoken: TpToken, mut err_buffer: Vec<u8>,
        func: unsafe extern "C" fn(
            u64,
            *mut ydb_buffer_t,
            *const ydb_buffer_t,
            i32,
            *const ydb_buffer_t,
            *mut ydb_buffer_t,
        ) -> c_int,
    ) -> YDBResult<Vec<u8>> {
        let mut err_buffer_t = Self::make_out_buffer_t(&mut err_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let t = self.subscripts.last_mut().unwrap_or(unsafe { self.variable.as_mut_vec() });
        let mut last_self_buffer;
        let status = loop {
            last_self_buffer = ydb_buffer_t {
                buf_addr: t.as_mut_ptr() as *mut _,
                len_alloc: t.capacity() as u32,
                len_used: t.len() as u32,
            };

            let status = unsafe {
                func(
                    tptoken.0,
                    &mut err_buffer_t,
                    varname.as_ptr(),
                    subscripts.len() as i32,
                    subscripts.as_ptr() as *const _,
                    &mut last_self_buffer,
                )
            };
            if status == YDB_ERR_INVSTRLEN {
                // New size should be size needed + (current size - len used)
                let new_size = (last_self_buffer.len_used - last_self_buffer.len_alloc) as usize;
                let new_size = new_size + (t.capacity() - t.len());
                t.reserve(new_size);
                continue;
            }
            break status;
        };
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        if status != YDB_OK as i32 {
            unsafe {
                err_buffer.set_len(min(err_buffer_t.len_alloc, err_buffer_t.len_used) as usize);
            }
            return Err(YDBError { message: err_buffer, status, tptoken });
        }
        unsafe {
            t.set_len(min(last_self_buffer.len_alloc, last_self_buffer.len_used) as usize);
        }
        Ok(err_buffer)
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
            buf_addr: self.variable.as_mut_ptr() as *mut _,
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
        let var = ydb_buffer_t {
            buf_addr: self.variable.as_ptr() as *mut _,
            len_alloc: self.variable.capacity() as u32,
            len_used: self.variable.len() as u32,
        }
        .into();
        let make_buffer = |vec: &Vec<_>| {
            ydb_buffer_t {
                // this cast is what's unsafe
                buf_addr: vec.as_ptr() as *mut _,
                len_alloc: vec.capacity() as u32,
                len_used: vec.len() as u32,
            }
            .into()
        };
        let subscripts = self.subscripts.iter().map(make_buffer).collect();
        (var, subscripts)
    }
}

#[repr(transparent)]
/// Because of this repr(transparent), it is safe to turn a
/// `*const ConstYDBBuffer` to `*const ydb_buffer_t`
struct ConstYDBBuffer(ydb_buffer_t);

impl ConstYDBBuffer {
    fn as_ptr(&self) -> *const ydb_buffer_t {
        &self.0
    }
}

impl From<ydb_buffer_t> for ConstYDBBuffer {
    fn from(buf: ydb_buffer_t) -> Self {
        Self(buf)
    }
}

// TODO: this is unsafe and could allow using the slice after it goes out of scope
// TODO: this is ok for now because `ConstYDBBuffer` is only used locally within a single function.
// TODO: possible fix: use `PhantomData` for `ConstYDBBuffer`
impl From<&[u8]> for ConstYDBBuffer {
    fn from(slice: &[u8]) -> Self {
        Self(ydb_buffer_t {
            buf_addr: slice.as_ptr() as *mut _,
            len_used: slice.len() as u32,
            len_alloc: slice.len() as u32,
        })
    }
}

/// Allow Key to mostly be treated as a `Vec<Vec<u8>>`,
/// but without `shrink_to_fit`, `drain`, or other methods that aren't relevant
impl Key {
    /// Remove all subscripts after the `i`th index.
    ///
    /// # See also
    /// - [`Vec::truncate()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.truncate)
    pub fn truncate(&mut self, i: usize) {
        self.subscripts.truncate(i);
    }
    /// Remove all subscripts, leaving only the `variable`.
    ///
    /// # See also
    /// - [`Vec::clear()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.clear)
    pub fn clear(&mut self) {
        self.subscripts.clear();
    }
    /// Add a new subscript, keeping all existing subscripts in place.
    ///
    /// # See also
    /// - [`Vec::push()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push)
    pub fn push(&mut self, subscript: Vec<u8>) {
        self.subscripts.push(subscript);
    }
    /// Remove the last subscript, keeping all other subscripts in place.
    ///
    /// Note that this will _not_ return the `variable` even if there are no subscripts present.
    ///
    /// # See also
    /// - [`Vec::pop()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.pop)
    pub fn pop(&mut self) -> Option<Vec<u8>> {
        self.subscripts.pop()
    }
}

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

/// The status returned from a callback passed to [`tp_st`]
///
/// [`tp_st`]: fn.tp_st.html
#[derive(Debug, Copy, Clone)]
pub enum TransactionStatus {
    /// Complete the transaction and commit all changes
    Ok = YDB_OK as isize,
    /// Undo changes specified in `locals_to_reset`, then restart the transaction
    Restart = YDB_TP_RESTART as isize,
    /// Abort the transaction and undo all changes
    Rollback = YDB_TP_ROLLBACK as isize,
}

type UserResult = Result<TransactionStatus, Box<dyn Error>>;

enum CallBackError {
    // the callback returned an error
    ApplicationError(Box<dyn Error>),
    // the callback panicked; this is the value `panic!` was called with
    Panic(Box<dyn std::any::Any + Send + 'static>),
}
/// Passes the callback function as a structure to the callback
struct CallBackStruct<'a> {
    cb: &'a mut dyn FnMut(TpToken) -> UserResult,
    /// Application error (not a YDBError)
    error: Option<CallBackError>,
}

extern "C" fn fn_callback(tptoken: u64, errstr: *mut ydb_buffer_t, tpfnparm: *mut c_void) -> i32 {
    assert!(!tpfnparm.is_null());
    assert!(!errstr.is_null());
    let callback_struct = unsafe { &mut *(tpfnparm as *mut CallBackStruct) };

    let mut cb = panic::AssertUnwindSafe(&mut callback_struct.cb);
    let tptoken = TpToken(tptoken);
    // this deref_mut() is because Rust is having trouble with type inferrence
    let retval = match panic::catch_unwind(move || cb.deref_mut()(tptoken)) {
        Ok(val) => val,
        Err(payload) => {
            callback_struct.error = Some(CallBackError::Panic(payload));
            return YDB_TP_ROLLBACK as i32;
        }
    };
    match retval {
        Ok(status) => status as i32,
        Err(x) => {
            // Try to cast into YDBError; if we can do that, return the error code
            // Else, rollback the transaction
            match x.downcast::<YDBError>() {
                Ok(err) => err.status,
                Err(err) => {
                    callback_struct.error = Some(CallBackError::ApplicationError(err));
                    YDB_TP_ROLLBACK as i32
                }
            }
        }
    }
}

/// Start a new transaction, where `f` is the transaction to execute.
///
/// The parameter `trans_id` is the name logged for the transaction.
///     If `trans_id` has the special value `"BATCH"`, durability is not enforced by YottaDB.
///     See the [C documentation] for details.
///
/// The argument passed to `f` is a [transaction processing token][threads and transactions].
///
/// # Rollbacks and Restarts
/// Application code can return a [`TransactionStatus`] in order to rollback or restart.
/// `tp_st` behaves as follows:
/// - If `f` panics, the transaction is rolled back and the panic resumes afterwards.
/// - If `f` returns `Ok(TransactionStatus)`,
///      the transaction will have the behavior documented under `TransactionStatus` (commit, restart, and rollback, respectively).
/// - If `f` returns an `Err(YDBError)`, the status from that error will be returned to the YottaDB engine.
///      As a result, if the status for the `YDBError` is `YDB_TP_RESTART`, the transaction will be restarted.
///      Otherwise, the transaction will be rolled back and the error returned from `tp_st`.
/// - If `f` returns any other `Err` variant, the transaction will be rolled back and the error returned from `tp_st`.
///
/// `f` must be `FnMut`, not `FnOnce`, since the YottaDB engine may
/// call `f` many times if necessary to ensure ACID properties.
/// This may affect your application logic; if you need to know how many
/// times the callback has been executed, get the [intrinsic variable][intrinsics]
/// [`$trestart`](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#trestart).
///
/// # Nested transactions
/// `f` may itself call `tp_st`. Such a call is called a 'nested transaction'.
/// If `f` receives a `YDBError` with a status of `YDB_TP_RESTART` or `YDB_TP_ROLLBACK` from a nested transaction,
/// it _must_ propagate that error back to the caller.
///
/// # Errors
/// - YDB_ERR_TPTIMEOUT - The transaction took more than [`$zmaxtptime`] seconds to execute,
///     where `$zmaxtptime` is an [intrinsic special variable][intrinsics].
/// - YDB_TP_ROLLBACK — application logic indicates that the transaction should not be committed.
/// - A `YDBError` returned by a YottaDB function called by `f`.
/// - Another arbitrary error returned by `f`.
///
/// # Examples
/// Rollback a transaction if an operation fails:
/// ```
/// use yottadb::{TpToken, TransactionStatus};
/// use yottadb::simple_api::{Key, tp_st};
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let var = Key::variable("tpRollbackTest");
/// var.set_st(TpToken::default(), Vec::new(), "initial value")?;
/// let maybe_err = tp_st(TpToken::default(), Vec::new(), |tptoken| {
///     fallible_operation()?;
///     var.set_st(tptoken, Vec::new(), "new value")?;
///     Ok(TransactionStatus::Ok)
/// }, "BATCH", &[]);
/// let expected_val: &[_] = if maybe_err.is_ok() {
///     b"new value"
/// } else {
///     b"initial value"
/// };
/// assert_eq!(var.get_st(TpToken::default(), Vec::new())?, expected_val);
/// # Ok(())
/// # }
///
/// fn fallible_operation() -> Result<(), &'static str> {
///     if rand::random() {
///         Ok(())
///     } else {
///         Err("the operation failed")
///     }
/// }
/// ```
///
/// Retry a transaction until it succeeds:
/// ```
/// use yottadb::{TpToken, TransactionStatus};
/// use yottadb::simple_api::tp_st;
///
/// tp_st(TpToken::default(), Vec::new(), |tptoken| {
///     if fallible_operation().is_ok() {
///         Ok(TransactionStatus::Ok)
///     } else {
///         Ok(TransactionStatus::Restart)
///     }
/// }, "BATCH", &[]).unwrap();
///
/// fn fallible_operation() -> Result<(), ()> {
///     if rand::random() {
///         Ok(())
///     } else {
///         Err(())
///     }
/// }
/// ```
///
/// # See Also
/// - [`context_api::Context::tp`](../context_api/struct.Context.html#method.tp)
/// - [More details about the underlying FFI call][C documentation]
/// - [Transaction Processing in YottaDB](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing)
/// - [Threads and Transaction Processing][threads and transactions]
///
/// [`$zmaxtptime`]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#zmaxtptime
/// [`TransactionStatus`]: ../simple_api/enum.TransactionStatus.html
/// [intrinsics]: index.html#intrinsic-variables
/// [threads and transactions]: https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#threads-and-transaction-processing
/// [C documentation]: https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-tp-s-ydb-tp-st
pub fn tp_st<F>(
    tptoken: TpToken, mut err_buffer: Vec<u8>, mut f: F, trans_id: &str, locals_to_reset: &[&str],
) -> Result<Vec<u8>, Box<dyn Error>>
where
    F: FnMut(TpToken) -> UserResult,
{
    let mut err_buffer_t = Key::make_out_buffer_t(&mut err_buffer);

    let mut locals: Vec<ConstYDBBuffer> = Vec::with_capacity(locals_to_reset.len());
    for local in locals_to_reset.iter() {
        locals.push(
            ydb_buffer_t {
                buf_addr: local.as_ptr() as *const _ as *mut _,
                len_alloc: local.len() as u32,
                len_used: local.len() as u32,
            }
            .into(),
        );
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
            CallBackError::ApplicationError(err) => Err(err),
            // reraise the panic now that we're past the FFI barrier
            CallBackError::Panic(payload) => panic::resume_unwind(payload),
        }
    } else {
        // a YDB error occurred; reuse out_buffer to return an error
        unsafe {
            err_buffer.set_len(min(err_buffer_t.len_used, err_buffer_t.len_alloc) as usize);
        }
        Err(Box::new(YDBError { message: err_buffer, status: status as i32, tptoken }))
    }
}

/// Delete all local variables _except_ for those passed in `saved_variable`.
///
/// Passing an empty `saved_variables` slice deletes all local variables.
/// Attempting to save a global or intrinsic variable is an error.
///
/// # Errors
/// - YDB_ERR_NAMECOUNT2HI if `saved_variables.len() > YDB_MAX_NAMES`
/// - YDB_ERR_INVVARNAME if attempting to save a global or intrinsic variable
/// - Another system [error return code](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
///
/// # Examples
///
/// ```
/// # fn main() -> yottadb::YDBResult<()> {
/// use yottadb::{TpToken, YDB_ERR_LVUNDEF};
/// use yottadb::simple_api::{Key, delete_excl_st};
///
/// // Create three variables and set all
/// let a = Key::variable("deleteExclTestA");
/// a.set_st(TpToken::default(), Vec::new(), "test data")?;
/// let b = Key::variable("deleteExclTestB");
/// b.set_st(TpToken::default(), Vec::new(), "test data 2")?;
/// let c = Key::variable("deleteExclTestC");
/// c.set_st(TpToken::default(), Vec::new(), "test data 3")?;
///
/// // Delete all variables except `a`
/// delete_excl_st(TpToken::default(), Vec::new(), &[&a.variable])?;
/// assert_eq!(a.get_st(TpToken::default(), Vec::new())?, b"test data");
/// assert_eq!(b.get_st(TpToken::default(), Vec::new()).unwrap_err().status, YDB_ERR_LVUNDEF);
/// assert_eq!(c.get_st(TpToken::default(), Vec::new()).unwrap_err().status, YDB_ERR_LVUNDEF);
///
/// // Delete `a` too
/// delete_excl_st(TpToken::default(), Vec::new(), &[])?;
/// assert_eq!(a.get_st(TpToken::default(), Vec::new()).unwrap_err().status, YDB_ERR_LVUNDEF);
///
/// # Ok(())
/// # }
/// ```
///
/// # See also
/// - The [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-delete-excl-s-ydb-delete-excl-st)
/// - [Local and global variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#local-and-global-variables)
/// - [Instrinsic special variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#intrinsic-special-variables)
pub fn delete_excl_st(
    tptoken: TpToken, err_buffer: Vec<u8>, saved_variables: &[&str],
) -> YDBResult<Vec<u8>> {
    use crate::craw::ydb_delete_excl_st;

    let varnames: Vec<ConstYDBBuffer> = saved_variables
        .iter()
        .map(|var| {
            ydb_buffer_t {
                buf_addr: var.as_ptr() as *mut _,
                len_used: var.len() as u32,
                len_alloc: var.len() as u32,
            }
            .into()
        })
        .collect();

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
/// # Errors
/// - [error codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
///
/// # Examples
///
/// ```
/// # use yottadb::YDBError;
/// # fn main() -> Result<(), YDBError> {
/// use yottadb::simple_api::str2zwr_st;
/// use yottadb::TpToken;
/// assert_eq!(str2zwr_st(TpToken::default(), Vec::new(), "💖".as_bytes())?, b"\"\xf0\"_$C(159,146,150)");
/// # Ok(())
/// # }
/// ```
///
/// # See also
/// - [Zwrite format](https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#zwrite-formatted)
/// - [`zwr2str_st`](fn.zwr2str_st.html), which deserializes a buffer in Zwrite format back to the original binary.
pub fn str2zwr_st(tptoken: TpToken, out_buf: Vec<u8>, original: &[u8]) -> YDBResult<Vec<u8>> {
    use crate::craw::ydb_str2zwr_st;

    let original_t = ConstYDBBuffer::from(original);
    resize_ret_call(tptoken, out_buf, |tptoken, err_buffer_p, out_buffer_p| unsafe {
        ydb_str2zwr_st(tptoken, err_buffer_p, original_t.as_ptr(), out_buffer_p)
    })
}

/// Given a buffer in 'Zwrite format', deserialize it to the original binary buffer.
///
/// # Errors
/// This function returns an empty array if `serialized` is not in Zwrite format.
/// It can also return another [error code](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code).
///
/// # Examples
///
/// ```
/// # use yottadb::YDBError;
/// # fn main() -> Result<(), YDBError> {
/// use yottadb::simple_api::zwr2str_st;
/// use yottadb::TpToken;
/// let out_buf = zwr2str_st(TpToken::default(), Vec::new(), b"\"\xf0\"_$C(159,146,150)")?;
/// assert_eq!(out_buf.as_slice(), "💖".as_bytes());
/// # Ok(())
/// # }
/// ```
///
/// # See also
/// - [Zwrite format](https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#zwrite-formatted)
/// - [str2zwr_st](fn.str2zwr_st.html), the inverse of `zwr2str_st`.
pub fn zwr2str_st(
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
/// # Errors
/// - `YDB_ERR_UNKNOWNSYSERR` if `status` is an unrecognized status code
///
/// # See also
/// - [`context_api::Context::message_t`](../context_api/struct.Context.html#method.message)
/// - [`impl Display for YDBError`][`impl Display`], which should meet most use cases for `message_t`.
/// - [Function return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#function-return-codes)
/// - [ZMessage codes](https://docs.yottadb.com/MessageRecovery/errormsgref.html#zmessage-codes)
/// - The [C documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-message-ydb-message-t)
///
/// [`impl Display`]: struct.YDBError.html#impl-Display
///
/// # Example
/// Look up the error message for an undefined local variable:
/// ```
/// use yottadb::{TpToken, YDB_ERR_LVUNDEF};
/// use yottadb::simple_api::{self, Key};
/// let key = Key::variable("oopsNotDefined");
/// let err = key.get_st(TpToken::default(), Vec::new()).unwrap_err();
/// assert_eq!(err.status, YDB_ERR_LVUNDEF);
/// let buf = simple_api::message_t(TpToken::default(), Vec::new(), err.status).unwrap();
/// let msg = String::from_utf8(buf).unwrap();
/// assert!(msg.contains("Undefined local variable"));
/// ```
pub fn message_t(tptoken: TpToken, out_buffer: Vec<u8>, status: i32) -> YDBResult<Vec<u8>> {
    resize_ret_call(tptoken, out_buffer, |tptoken, err_buffer_p, out_buffer_p| unsafe {
        ydb_message_t(tptoken, err_buffer_p, status, out_buffer_p)
    })
}

/// Return a string in the format `rustwr <rust wrapper version> <$ZYRELEASE>`
///
/// [`$ZYRELEASE`] is the [intrinsic variable] containing the version of the underlying C database
/// and `<rust wrapper version>` is the version of `yottadb` published to crates.io.
///
/// # Errors
/// No errors should occur in normal operation.
/// However, in case of system failure, an [error code] may be returned.
///
/// [error code]: https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code
/// [intrinsic variable]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#intrinsic-special-variables
/// [`$ZYRELEASE`]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#zyrelease
///
/// # Example
/// ```
/// use yottadb::{simple_api, TpToken};
/// let release = simple_api::release_t(TpToken::default(), Vec::new()).unwrap();
/// ```
pub fn release_t(tptoken: TpToken, out_buffer: Vec<u8>) -> YDBResult<String> {
    let zrelease = Key::variable("$ZYRELEASE").get_st(tptoken, out_buffer)?;
    let zrelease = String::from_utf8(zrelease).expect("$ZRELEASE was not valid UTF8");
    Ok(format!("rustwr {} {}", env!("CARGO_PKG_VERSION"), zrelease))
}

/// Acquires locks specified in `locks` and releases all others.
///
/// This operation is atomic. If any lock cannot be acquired, all locks are released.
/// The `timeout` specifies the maximum time to wait before returning an error.
/// If no locks are specified, all locks are released.
///
/// Note that YottaDB locks are per-process, not per-thread.
///
/// # Limitations
///
/// For implementation reasons, there is a hard limit to the number of `Key`s that can be passed in `locks`:
// floor( (36 - 4)/3 ) = 10
/// - 64-bit: 10 `Key`s
// floor( (36 - 7)/3 ) = 9
/// - 32-bit: 9  `Key`s
///
/// If more than this number of keys are passed, `lock_st` will return `YDB_ERR_MAXARGCNT`.
///
/// For implementation reasons, `lock_st` only works on 64-bit platforms, or on 32-bit ARM.
///
/// `lock_st` will not be compiled on 16, 8, or 128 bit platforms
/// (i.e. will fail with 'cannot find function `lock_st` in module `yottadb::simple_api`').
///
/// On non-ARM 32-bit platforms, the compiler will allow `lock_st` to be called,
/// but it will have unspecified behavior and has not been tested.
/// Use [`Key::lock_incr_st`] and [`Key::lock_decr_st`] instead.
///
/// # Errors
///
/// Possible errors for this function include:
/// - `YDB_LOCK_TIMEOUT` if all locks could not be acquired within the timeout period.
///   In this case, no locks are acquired.
/// - `YDB_ERR_TIME2LONG` if `timeout` is greater than `YDB_MAX_TIME_NSEC`
/// - `YDB_ERR_MAXARGCNT` if too many locks have been passed (see [Limitations](#limitations))
/// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
///
/// # Examples
/// ```
/// use std::slice;
/// use std::time::Duration;
/// use yottadb::TpToken;
/// use yottadb::simple_api::{Key, lock_st};
///
/// // acquire a new lock
/// let a = Key::variable("lockA");
/// // using `from_ref` here allows us to use `a` later without moving it
/// lock_st(TpToken::default(), Vec::new(), Duration::from_secs(1), slice::from_ref(&a)).unwrap();
///
/// // acquire multiple locks
/// let locks = vec![a, Key::variable("lockB")];
/// lock_st(TpToken::default(), Vec::new(), Duration::from_secs(1), &locks).unwrap();
///
/// // release all locks
/// lock_st(TpToken::default(), Vec::new(), Duration::from_secs(1), &[]).unwrap();
/// ```
///
/// # See also
///
/// - The C [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-lock-s-ydb-lock-st)
/// - [Locks](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#locks)
/// - [`context_api::Context::lock`](../context_api/struct.Context.html#method.lock)
///
/// [`Key::lock_incr_st`]: struct.Key.html#method.lock_incr_st
/// [`Key::lock_decr_st`]: struct.Key.html#method.lock_decr_st
#[cfg(any(target_pointer_width = "64", target_pointer_width = "32"))]
pub fn lock_st(
    tptoken: TpToken, mut out_buffer: Vec<u8>, timeout: Duration, locks: &[Key],
) -> YDBResult<Vec<u8>> {
    use std::convert::TryFrom;
    use crate::craw::{
        YDB_ERR_MAXARGCNT, YDB_ERR_TIME2LONG, MAXVPARMS, ydb_lock_st, ydb_call_variadic_plist_func,
        gparam_list,
    };
    // `ydb_lock_st` is hard to work with because it uses variadic arguments.
    // The only way to pass a variable number of arguments in Rust is to pass a slice
    // or use a macro (i.e. know the number of arguments ahead of time).

    // To get around this, `lock_st` calls the undocumented `ydb_call_variadic_plist_func` function.
    // `ydb_call_variadic_plist_func` takes the function to call, and a { len, args } struct.
    // `args` is required to be stack-allocated and has a maximum capacity of MAXVPARMS.
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
    let mut arg = [0 as Void; MAXVPARMS as usize];
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
        if i + 2 >= MAXVPARMS as usize {
            return Err(YDBError {
                status: YDB_ERR_MAXARGCNT,
                message: format!("Expected at most {} arguments, got {}", MAXVPARMS, i)
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

    let args = gparam_list { n: i as isize, arg };
    let status = unsafe {
        // The types on `ydb_call_variadic_plist_func` are not correct.
        // Additionally, `ydb_lock_st` on its own is a unique zero-sized-type (ZST):
        // See https://doc.rust-lang.org/reference/types/function-item.html#function-item-types for more details on function types
        // and https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts for details on ZSTs.
        // This `as *const ()` turns the unique ZST for `ydb_lock_st` into a proper function pointer.
        // Without the `as` cast, `transmute` will return `1_usize` and `ydb_call` will subsequently segfault.
        let ydb_lock_as_vplist_func = std::mem::transmute(ydb_lock_st as *const ());
        ydb_call_variadic_plist_func(Some(ydb_lock_as_vplist_func), &args as *const _ as usize)
    };

    // We could end up with a buffer of a larger size if we couldn't fit the error string
    // into the out_buffer, so make sure to pick the smaller size
    let len = min(err_buffer_t.len_used, err_buffer_t.len_alloc) as usize;
    unsafe {
        out_buffer.set_len(len);
    }

    if status != YDB_OK as c_int {
        Err(YDBError { message: out_buffer, status, tptoken })
    } else {
        Ok(out_buffer)
    }
}

/// See documentation for `non_allocating_call` for more details.
///
/// F: FnMut(tptoken, err_buffer_t, out_buffer_t) -> status
// This has to be public so that it can be used by `ci_t!`.
// However, it is not a supported part of the API.
#[doc(hidden)]
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

/// See documentation for `non_allocating_ret_call` for more details.
///
/// F: FnMut(tptoken, err_buffer_t, out_buffer_t) -> status
fn resize_ret_call<F>(tptoken: TpToken, mut out_buffer: Vec<u8>, mut func: F) -> YDBResult<Vec<u8>>
where
    F: FnMut(u64, *mut ydb_buffer_t, *mut ydb_buffer_t) -> c_int,
{
    let status = loop {
        let mut out_buffer_t = Key::make_out_buffer_t(&mut out_buffer);
        // NOTE: it is very important that this makes a copy of `out_buffer_t`:
        // otherwise, on `INVSTRLEN`, when YDB tries to set len_used it will overwrite the necessary
        // capacity with the length of the string.
        let mut err_buffer_t = out_buffer_t;
        // Do the call
        let status = func(tptoken.into(), &mut err_buffer_t, &mut out_buffer_t);
        // Handle resizing the buffer, if needed
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize(out_buffer_t.len_used as usize, 0);
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
        Err(YDBError { tptoken, message: out_buffer, status })
    } else {
        Ok(out_buffer)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use serial_test::serial;
    use proptest::prelude::*;
    use crate::*;
    use super::*;

    fn arb_key() -> impl Strategy<Value = Key> {
        any::<(String, Vec<Vec<u8>>)>().prop_map(|(var, subs)| Key::new(var, &subs))
    }

    fn arb_keys() -> impl Strategy<Value = Vec<Key>> {
        proptest::collection::vec(arb_key(), 0..12)
    }

    #[test]
    fn can_make_key() {
        Key::variable("key");
    }

    #[test]
    fn can_make_key_with_subscripts() {
        Key::new("^hello", &["world"]);
    }

    #[test]
    fn basic_set_and_get_st() {
        let mut result = Vec::with_capacity(1);
        let key = Key::variable("^basicSetGet");

        // Try setting a value
        result = key.set_st(YDB_NOTTP, result, b"Hello world!").unwrap();
        // Then try getting the value we set
        result = key.get_st(YDB_NOTTP, result).unwrap();
        assert_eq!(result, b"Hello world!");

        // Try an error where the error message is shorter than the retrieved value
        let val: &[_] = &[b'a'; 1000];
        key.set_st(YDB_NOTTP, result, &val).unwrap();
        // Then try getting the value we set
        result = key.get_st(YDB_NOTTP, Vec::new()).unwrap();
        assert_eq!(result, val);
    }

    #[test]
    fn ydb_get_st_error() {
        let key = Key::variable("^helloDoesntExists");
        let err = key.get_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, crate::craw::YDB_ERR_GVUNDEF);

        let key = Key::variable("helloDoesntExists");
        let err = key.get_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, crate::craw::YDB_ERR_LVUNDEF);
    }

    #[test]
    fn ydb_set_st_error() {
        let key = Key::variable("$ZCHSET");
        let err = key.set_st(YDB_NOTTP, Vec::new(), "some val").unwrap_err();
        assert_eq!(err.status, craw::YDB_ERR_SVNOSET)
        // other errors tested in `common_errors`
    }

    #[test]
    fn ydb_data_st() {
        let err_buf = Vec::with_capacity(1);
        let mut key = Key::variable("testDataSt");

        // should be empty to start
        let (retval, err_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(retval, DataReturn::NoData);

        // set the node
        let err_buf = key.set_st(YDB_NOTTP, err_buf, "some data").unwrap();
        let (retval, err_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(retval, DataReturn::ValueData);

        // set node and child
        key.push("some subscript".into());
        let err_buf = key.set_st(YDB_NOTTP, err_buf, "subscript data").unwrap();
        key.pop();
        let (retval, err_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(retval, DataReturn::ValueTreeData);

        // delete the node, keep the child
        let err_buf = key.delete_st(YDB_NOTTP, err_buf, DeleteType::DelNode).unwrap();
        let (retval, err_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(retval, DataReturn::TreeData);

        // delete the tree
        let err_buf = key.delete_st(YDB_NOTTP, err_buf, DeleteType::DelTree).unwrap();
        let (retval, _) = key.data_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(retval, DataReturn::NoData);
    }

    #[test]
    fn ydb_delete_st() {
        let mut result = Vec::with_capacity(1);
        let key = Key::variable("^helloDeleteMe");

        // Try setting a value
        result = key.set_st(YDB_NOTTP, result, b"Hello world!").unwrap();
        // Check data
        let (retval, mut result) = key.data_st(YDB_NOTTP, result).unwrap();
        assert_ne!(retval, DataReturn::NoData);
        // Delete the value
        result = key.delete_st(YDB_NOTTP, result, DeleteType::DelNode).unwrap();
        let (retval, _) = key.data_st(YDB_NOTTP, result).unwrap();
        // Check for no data
        assert_eq!(retval, DataReturn::NoData);
    }

    #[test]
    fn ydb_delete_excl_st() {
        let out_buf = Vec::new();
        let mut key = Key::variable("deleteExcl");

        // Set a few values
        let out_buf = key.set_st(YDB_NOTTP, out_buf, b"some value").unwrap();
        key.variable = "deleteExcl2".into();
        let out_buf = key.set_st(YDB_NOTTP, out_buf, b"some value").unwrap();

        // Delete `deleteExcl2`, saving `deleteExcl`
        let out_buf = delete_excl_st(YDB_NOTTP, out_buf, &["deleteExcl"]).unwrap();
        // Check data
        let (data_type, out_buf) = key.data_st(YDB_NOTTP, out_buf).unwrap();
        assert_eq!(data_type, DataReturn::NoData);
        key.variable = "deleteExcl".into();
        let (data_type, out_buf) = key.data_st(YDB_NOTTP, out_buf).unwrap();
        assert_eq!(data_type, DataReturn::ValueData);

        // Delete `deleteExcl`
        let out_buf = delete_excl_st(YDB_NOTTP, out_buf, &[]).unwrap();
        // Make sure it was actually deleted
        let (data_type, out_buf) = key.data_st(YDB_NOTTP, out_buf).unwrap();
        assert_eq!(data_type, DataReturn::NoData);

        // Saving a global/intrinsic variable should be an error
        use crate::craw::YDB_ERR_INVVARNAME;
        let err = delete_excl_st(YDB_NOTTP, out_buf, &["^global"]).unwrap_err();
        assert_eq!(err.status, YDB_ERR_INVVARNAME);
        let err = delete_excl_st(YDB_NOTTP, Vec::new(), &["$ZSTATUS"]).unwrap_err();
        assert_eq!(err.status, YDB_ERR_INVVARNAME);

        // Saving a variable that doesn't exist should do nothing and return YDB_OK.
        delete_excl_st(YDB_NOTTP, Vec::new(), &["local"]).unwrap();

        // Check for `YDB_ERR_NAMECOUNT2HI` if too many params are passed
        use crate::craw::{YDB_ERR_NAMECOUNT2HI, YDB_MAX_NAMES};
        let vars = vec!["hello"; YDB_MAX_NAMES as usize + 1];
        let err = delete_excl_st(YDB_NOTTP, Vec::new(), &vars).unwrap_err();
        assert_eq!(err.status, YDB_ERR_NAMECOUNT2HI);
    }

    #[test]
    fn ydb_incr_st() {
        let err_buf = Vec::with_capacity(1);
        let key = Key::variable("^helloIncrementMe");
        let err_buf = key.set_st(YDB_NOTTP, err_buf, "0").unwrap();

        let err_buf = key.incr_st(YDB_NOTTP, err_buf, None).unwrap();
        let out_buf = key.get_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(&out_buf, b"1");

        let num = 1500.to_string().into_bytes();
        let err_buf = key.incr_st(YDB_NOTTP, out_buf, Some(&num)).unwrap();
        let out_buf = key.get_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(&out_buf, b"1501");

        // make sure that incr_st works even if the node doesn't exist yet
        let err_buf = key.delete_st(YDB_NOTTP, out_buf, DeleteType::DelNode).unwrap();
        let err_buf = key.incr_st(YDB_NOTTP, err_buf, None).unwrap();
        let out_buf = key.get_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(&out_buf, b"1");

        // Make sure the value is converted when it isn't a number
        let err_buf = key.set_st(YDB_NOTTP, out_buf, "not a number").unwrap();
        let err_buf = key.incr_st(YDB_NOTTP, err_buf, None).unwrap();
        let out_buf = key.get_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(&out_buf, b"1");

        // Clean up
        key.delete_st(YDB_NOTTP, out_buf, DeleteType::DelNode).unwrap();
    }

    // Return the number of locks held for `var`
    pub(crate) fn lock_count(var: &str) -> usize {
        use std::os::raw::{c_char, c_ulong};
        use crate::craw::ydb_string_t;

        fn make_out_str_t(slice: &mut [u8]) -> ydb_string_t {
            ydb_string_t {
                address: slice.as_mut_ptr() as *mut c_char,
                length: slice.len() as c_ulong,
            }
        }

        std::env::set_var("ydb_routines", "examples/m-ffi");
        std::env::set_var("ydb_ci", "examples/m-ffi/calltab.ci");

        let m_code = CString::new("zshvar").unwrap();
        let mut stored_var = Vec::from("outputvar");
        let mut output_var = Vec::from("l");
        let mut output_var_t = make_out_str_t(&mut output_var);
        let mut stored_var_t = make_out_str_t(&mut stored_var);

        let mut err_buf = unsafe {
            ci_t!(
                YDB_NOTTP,
                Vec::new(),
                &m_code,
                &mut output_var_t as *mut _,
                &mut stored_var_t as *mut _
            )
        }
        .unwrap();

        // look for the right key
        let mut count = 1;
        let mut key = Key::new(String::from_utf8(stored_var).unwrap(), &["L", "1"]);
        loop {
            let (data, loop_buf) = key.data_st(YDB_NOTTP, err_buf).unwrap();
            if data == DataReturn::NoData {
                return 0;
            }
            let val = key.get_st(YDB_NOTTP, loop_buf).unwrap();
            // looks like `LOCK x LEVEL=1`
            let locks = String::from_utf8(val).unwrap();
            let mut groups = locks.split_whitespace();
            assert_eq!(groups.next(), Some("LOCK"));
            let name = groups.next().unwrap();
            if name == var {
                let locks = groups.next().unwrap()["LEVEL=".len()..].parse().unwrap();
                assert_ne!(locks, 0);
                return locks;
            }
            count += 1;
            key[1] = count.to_string().into_bytes();
            err_buf = locks.into_bytes();
        }
    }
    #[test]
    #[serial]
    fn ydb_lock_incr_decr_st() {
        // Create a new lock
        let err_buf = Vec::new();
        let key = Key::variable("simpleIncrLock");
        // Increment it twice
        let err_buf = key.lock_incr_st(YDB_NOTTP, err_buf, Duration::from_millis(500)).unwrap();
        let err_buf = key.lock_incr_st(YDB_NOTTP, err_buf, Duration::from_secs(0)).unwrap();
        // Make sure the lock count is correct
        assert_eq!(lock_count(&key.variable), 2);

        // Decrement it twice
        let err_buf = key.lock_decr_st(YDB_NOTTP, err_buf).unwrap();
        key.lock_decr_st(YDB_NOTTP, err_buf).unwrap();
        // Make sure the lock has been released
        assert_eq!(lock_count(&key.variable), 0);

        // Test for TIME2LONG
        for &time in
            &[std::u64::MAX, std::u32::MAX.into(), (std::u32::MAX / 2).into(), 0xf00_0000_0000_0000]
        {
            let res = key.lock_incr_st(YDB_NOTTP, Vec::new(), Duration::from_secs(time));
            assert!(res.unwrap_err().status == craw::YDB_ERR_TIME2LONG);
        }
    }

    #[test]
    #[serial]
    fn ydb_lock_st() {
        use crate::craw::{YDB_ERR_MAXARGCNT, YDB_ERR_TIME2LONG};

        // Test global and local locks
        for &lock in &["ydbLock", "^ydbLock"] {
            let key = Key::variable(lock);
            assert_eq!(lock_count(&key.variable), 0);
            // Acquire the lock
            lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), std::slice::from_ref(&key))
                .unwrap();
            assert_eq!(lock_count(&key.variable), 1);
            // Release all locks
            lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &[]).unwrap();
            assert_eq!(lock_count(&key.variable), 0);
        }

        // Test for too many locks
        let mut locks = Vec::new();
        for c in b'a'..=b'z' {
            let var = String::from_utf8([c].to_vec()).unwrap();
            locks.push(Key::variable(var));
        }
        let res = lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &locks);
        assert!(res.unwrap_err().status == YDB_ERR_MAXARGCNT);

        // Test for TIME2LONG
        for &time in
            &[std::u64::MAX, std::u32::MAX.into(), (std::u32::MAX / 2).into(), 0xf00_0000_0000_0000]
        {
            let res = lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(time), &[]);
            assert!(res.unwrap_err().status == YDB_ERR_TIME2LONG);
        }

        // Test for the maximum number of locks
        locks.clear();
        #[cfg(target_pointer_width = "64")]
        let max = 10;
        #[cfg(target_pointer_width = "32")]
        let max = 9;
        for i in 0..max {
            // YDB variables can't start with a number
            let mut s = String::from("a");
            s.push_str(&i.to_string());
            locks.push(Key::variable(s));
        }
        lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &locks).unwrap();
        for lock in &locks {
            assert_eq!(lock_count(&lock.variable), 1);
        }
        locks.push(Key::variable("oneTooMany"));
        let err = lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &locks).unwrap_err();
        assert_eq!(err.status, YDB_ERR_MAXARGCNT);
    }

    #[test]
    fn ydb_node_next_self_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeNext", "shire");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        key[0] = Vec::from("hyrule");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        key[0] = Vec::from("a");
        key.node_next_self_st(YDB_NOTTP, result).unwrap();
    }

    #[test]
    fn ydb_node_next_self_extra_node_st() {
        let mut result = Vec::with_capacity(1);
        let value = b"Hello world!";
        let mut key = make_key!("^helloNodeNext2", "worlds", "shire");
        result = key.set_st(YDB_NOTTP, result, value).unwrap();
        key[1] = Vec::from("hyrule");
        result = key.set_st(YDB_NOTTP, result, value).unwrap();
        key.truncate(2);
        key.node_next_self_st(YDB_NOTTP, result).unwrap();

        // YDB_ERR_NODEEND
        // make sure NODEEND is still returned if we call multiple times in a row
        for _ in 0..10 {
            let err = key.node_next_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
            assert_eq!(err.status, craw::YDB_ERR_NODEEND);
        }

        // now test it for node_prev_self
        key.node_prev_self_st(YDB_NOTTP, Vec::new()).unwrap();
        assert_eq!(key[1], b"hyrule");
        for _ in 0..10 {
            let err = key.node_prev_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
            assert_eq!(err.status, craw::YDB_ERR_NODEEND);
        }
    }

    #[test]
    fn ydb_node_prev_self_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeprev", "shire");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        key[0] = Vec::from("hyrule");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        key[0] = Vec::from("z");
        if let Err(err) = key.node_prev_self_st(YDB_NOTTP, result) {
            panic!("{}", err);
        }
    }

    #[test]
    fn ydb_node_prev_self_extra_node_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeprev2", "worlds", "shire");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        key[1] = Vec::from("hyrule");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        key.truncate(2);
        key[0] = Vec::from("z");
        key.node_prev_self_st(YDB_NOTTP, result).unwrap();
    }

    #[test]
    fn ydb_subscript_next() {
        let mut result = Vec::with_capacity(1);
        let mut key = make_key!("^helloSubNext", "a");
        result = key.set_st(YDB_NOTTP, result, b"Hello world!").unwrap();
        key[0] = Vec::with_capacity(1);
        result = key.sub_next_st(YDB_NOTTP, result).unwrap();
        assert_eq!(result, b"a");
        key[0] = vec![b'a'];
        key.delete_st(YDB_NOTTP, Vec::new(), DeleteType::DelNode).unwrap();

        key[0] = vec![b'a'; 100];
        key.delete_st(YDB_NOTTP, Vec::new(), DeleteType::DelNode).unwrap();

        // Test a subscript with an INVSTRLEN shorter than the required capacity
        key[0] = vec![b'a'; 150];
        key.set_st(YDB_NOTTP, result, "some val").expect("set_st");

        key[0] = vec![b'a'];
        let subs = key.sub_next_st(YDB_NOTTP, Vec::new()).expect("sub_next");
        assert_eq!(subs.as_slice(), &[b'a'; 150][..]);

        key[0] = vec![b'b'];
        let subs = key.sub_prev_st(YDB_NOTTP, Vec::new()).expect("sub_prev");
        assert_eq!(subs.as_slice(), &[b'a'; 150][..]);
        key[0] = subs;
        key.delete_st(YDB_NOTTP, Vec::new(), DeleteType::DelTree).unwrap();
    }

    #[test]
    fn ydb_subscript_prev() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubprev", "b");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        key[0] = Vec::from("z");
        result = key.sub_prev_st(YDB_NOTTP, result).unwrap();
        assert_eq!(result, Vec::from("b"));
    }

    #[test]
    fn ydb_subscript_next_self() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubNext2", "shire");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        // TODO: we need a better way to expand these buffers in the _self function
        key[0] = Vec::with_capacity(1);
        key.sub_next_self_st(YDB_NOTTP, result).unwrap();
        assert_eq!(key[0], Vec::from("shire"));
    }

    #[test]
    fn ydb_subscript_prev_self() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubprev2", "shire");
        result = key.set_st(YDB_NOTTP, result, &value).unwrap();
        key[0] = Vec::from("z");
        key.sub_prev_self_st(YDB_NOTTP, result).unwrap();
        assert_eq!(key[0], Vec::from("shire"));
    }

    #[test]
    fn ydb_tp_st() {
        use crate::craw;

        // Variables are persisted after a transaction
        let key = Key::variable("tpPersistence");
        let result = Vec::with_capacity(1);
        let result = tp_st(
            YDB_NOTTP,
            result,
            |tptoken| {
                key.set_st(tptoken, Vec::new(), "value").unwrap();
                Ok(TransactionStatus::Ok)
            },
            "BATCH",
            &[],
        )
        .unwrap();
        assert_eq!(key.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"value");

        // user error
        let err = tp_st(YDB_NOTTP, result, |_| Err("oops!".into()), "BATCH", &[]).unwrap_err();
        assert_eq!(err.to_string(), "oops!");

        // ydb error
        let vec = Vec::with_capacity(10);
        let err = tp_st(
            YDB_NOTTP,
            vec,
            |tptoken| {
                let key = make_key!("hello");
                key.get_st(tptoken, Vec::with_capacity(1024))?;
                unreachable!();
            },
            "BATCH",
            &[],
        )
        .unwrap_err();
        assert!(err.downcast::<YDBError>().unwrap().status == craw::YDB_ERR_LVUNDEF);

        // TPTOODEEP
        fn call_forever(tptoken: TpToken) -> UserResult {
            tp_st(tptoken, Vec::new(), call_forever, "BATCH", &[])?;
            Ok(TransactionStatus::Ok)
        }
        let err = call_forever(YDB_NOTTP).unwrap_err();
        match err.downcast::<YDBError>() {
            Ok(err) if err.status == craw::YDB_ERR_TPTOODEEP => {}
            other => panic!("expected ERR_TPTOODEEP, got {:?}", other),
        }

        // Check for `YDB_ERR_NAMECOUNT2HI` if too many params are passed
        let vars = vec!["hello"; craw::YDB_MAX_NAMES as usize + 1];
        let err = tp_st(YDB_NOTTP, Vec::new(), |_| Ok(TransactionStatus::Ok), "BATCH", &vars)
            .unwrap_err();
        match err.downcast::<YDBError>() {
            Ok(err) => assert_eq!(err.status, craw::YDB_ERR_NAMECOUNT2HI),
            other => panic!("expected ERR_TPTOODEEP, got {:?}", other),
        }

        // Check that TLEVEL is set properly
        let tlevel = Key::variable("$TLEVEL");
        assert_eq!(&tlevel.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"0");
        tp_st(
            YDB_NOTTP,
            Vec::new(),
            |tptoken| {
                let val = tlevel.get_st(tptoken, Vec::new()).unwrap();
                assert_eq!(&val, b"1");
                Ok(TransactionStatus::Ok)
            },
            "BATCH",
            &[],
        )
        .unwrap();
        assert_eq!(&tlevel.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"0");
    }

    #[test]
    fn nested_transaction() {
        let mut first_run = true;
        tp_st(
            YDB_NOTTP,
            Vec::new(),
            |tptoken| {
                // Save this value because it's about to change
                let captured_first_run = first_run;
                // Some inner transaction that returns a RESTART
                // The restart is propagated upward by the `?`,
                // since `tp_st` returns YDBError { status: YDB_TP_RESTART }.
                let res = tp_st(
                    tptoken,
                    Vec::new(),
                    |_| {
                        if first_run {
                            first_run = false;
                            Ok(TransactionStatus::Restart)
                        } else {
                            Ok(TransactionStatus::Ok)
                        }
                    },
                    "BATCH",
                    &[],
                );
                // Make sure `RESTART` is returned the first time
                if captured_first_run {
                    let err = res.unwrap_err();
                    let status = err.downcast_ref::<YDBError>().unwrap().status;
                    assert_eq!(status, YDB_TP_RESTART);
                    Err(err)
                } else {
                    // Make sure `OK` is return the second time
                    res.unwrap();
                    Ok(TransactionStatus::Ok)
                }
            },
            "BATCH",
            &[],
        )
        .unwrap();
    }

    #[test]
    #[serial]
    fn restart_resets_locals() {
        let a = Key::variable("tpResetsLocals");

        for locals in &[&["*"][..], &[a.variable.as_str()], &[&a.variable, "b", "c"]] {
            let mut i = 0;

            a.set_st(YDB_NOTTP, Vec::new(), "initial value").unwrap();
            assert_eq!(&a.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"initial value");

            // make sure `a` is reset after each call
            let closure = |tptoken| {
                assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"initial value");
                a.set_st(tptoken, Vec::new(), "new value").unwrap();
                assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"new value");
                if i == 3 {
                    Ok(TransactionStatus::Ok)
                } else {
                    i += 1;
                    Ok(TransactionStatus::Restart)
                }
            };
            tp_st(YDB_NOTTP, Vec::new(), closure, "BATCH", locals).unwrap();
        }

        // now make sure that locals are not reset unless specified
        for locals in &[&["b"][..], &["b", "c", "d"], &[]] {
            a.set_st(YDB_NOTTP, Vec::new(), "initial value").unwrap();
            assert_eq!(&a.get_st(YDB_NOTTP, Vec::new()).unwrap(), b"initial value");

            let mut i = 0;
            tp_st(
                YDB_NOTTP,
                Vec::new(),
                |tptoken| {
                    if i == 0 {
                        assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"initial value");
                    } else {
                        assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"new value");
                    }
                    a.set_st(tptoken, Vec::new(), "new value").unwrap();
                    assert_eq!(&a.get_st(tptoken, Vec::new()).unwrap(), b"new value");
                    if i == 3 {
                        Ok(TransactionStatus::Ok)
                    } else {
                        i += 1;
                        Ok(TransactionStatus::Restart)
                    }
                },
                "BATCH",
                locals,
            )
            .unwrap();
        }
    }

    #[test]
    #[should_panic]
    fn panic_in_cb() {
        tp_st(YDB_NOTTP, Vec::with_capacity(10), |_| panic!("oh no!"), "BATCH", &[]).unwrap_err();
    }

    #[test]
    fn ydb_message_t() {
        use crate::craw;
        let mut err =
            YDBError { message: Vec::new(), status: craw::YDB_ERR_GVUNDEF, tptoken: YDB_NOTTP };
        assert!(err.to_string().contains("%YDB-E-GVUNDEF, Global variable undefined"));

        // make sure it works even if it has to resize the out_buffer
        err.status = 150380370;
        let expected = "%YDB-E-INVTRNSQUAL, Invalid TRANSACTION qualifier.  Specify only one of TRANSACTION=[NO]SET or TRANSACTION=[NO]KILL.";
        assert!(
            err.to_string().contains(expected),
            "expected INVTRNSQUAL, got {}",
            err.to_string()
        );

        err.status = 10001;
        assert!(err.to_string().contains("%SYSTEM-E-ENO10001, Unknown error 10001"));
    }

    proptest::proptest! {
        #[test]
        fn ydb_zwr2str_st_proptest(s in ".*") {
            let serialized = str2zwr_st(YDB_NOTTP, Vec::new(), s.as_bytes()).unwrap();
            let deserialized = zwr2str_st(YDB_NOTTP, Vec::new(), &serialized).unwrap();
            assert_eq!(s.as_bytes(), deserialized.as_slice());
        }
        #[test]
        fn ydb_zwr2str_st_bytes_proptest(s: Vec<u8>) {
            let serialized = str2zwr_st(YDB_NOTTP, Vec::new(), &s).unwrap();
            let deserialized = zwr2str_st(YDB_NOTTP, Vec::new(), &serialized).unwrap();
            assert_eq!(s, deserialized);
        }
        #[test]
        fn no_invlnpairlist_lock_proptest(timeout: Duration, keys in arb_keys()) {
            // lock_st should never return `INVLNPAIRLIST`
            match lock_st(YDB_NOTTP, Vec::new(), timeout, &keys) {
                Err(YDBError { status: craw::YDB_ERR_INVLNPAIRLIST, .. }) => panic!("lock_st should never return YDB_ERR_INVLNPAIRLIST"),
                _ => {}
            }
        }
        #[test]
        // no Rust Simple API should ever return INVSTRLEN or INSUFFSUBS
        fn no_invalid_errors_proptest(key in arb_key(), value: Vec<u8>, b: bool) {
            fn assert_not_invalid<T>(res: YDBResult<T>) {
                match res {
                    Err(ydberr) if ydberr.status == YDB_ERR_INVSTRLEN => {
                        panic!("function returned YDB_ERR_INVSTRLEN");
                    }
                    Err(ydberr) if ydberr.status == YDB_ERR_INSUFFSUBS => {
                        panic!("function returned YDB_ERR_INVSTRLEN");
                    }
                    _ => {}
                };
            }
            let tptoken = YDB_NOTTP;
            assert_not_invalid(key.get_st(tptoken, vec![]));
            assert_not_invalid(key.set_st(tptoken, vec![], &value));
            assert_not_invalid(key.data_st(tptoken, vec![]));
            assert_not_invalid(key.delete_st(tptoken, vec![], if b { DeleteType::DelTree } else { DeleteType::DelNode }));
            assert_not_invalid(key.incr_st(tptoken, vec![], if b { Some(&value) } else { None }));
            assert_not_invalid(key.lock_incr_st(tptoken, vec![], Duration::from_secs(0)));
            assert_not_invalid(key.lock_decr_st(tptoken, vec![]));
            assert_not_invalid(key.clone().node_next_self_st(tptoken, vec![]));
            assert_not_invalid(key.clone().node_prev_self_st(tptoken, vec![]));
            assert_not_invalid(key.clone().sub_next_st(tptoken, vec![]));
            assert_not_invalid(key.clone().sub_prev_st(tptoken, vec![]));
        }
    }

    #[test]
    fn ydb_zwr2str_st() {
        let s = "hello good morning this is a very very long string that you'll have to resize";
        let serialized = str2zwr_st(YDB_NOTTP, Vec::new(), s.as_bytes()).unwrap();
        let deserialized = zwr2str_st(YDB_NOTTP, Vec::new(), &serialized).unwrap();
        assert_eq!(s.as_bytes(), deserialized.as_slice());

        // found by proptest
        let s = "🕴\'\u{c3d07}\u{106179}\u{1b}\u{a8c00}\u{c41b6}";
        println!("{}", s.len());
        let serialized = str2zwr_st(YDB_NOTTP, Vec::new(), s.as_bytes()).unwrap();
        let deserialized = zwr2str_st(YDB_NOTTP, Vec::new(), &serialized).unwrap();
        assert_eq!(s.as_bytes(), deserialized.as_slice());
    }

    #[test]
    fn empty_err_buf() {
        use crate::craw::YDB_ERR_GVUNDEF;
        let key = Key::variable("^doesnotexist");
        let err_buf = Vec::new();
        let res = key.get_st(YDB_NOTTP, err_buf);
        assert_eq!(res.unwrap_err().status, YDB_ERR_GVUNDEF);
    }
    #[test]
    fn empty_subscript() {
        use crate::craw::YDB_ERR_LVUNDEF;

        let mut key = make_key!("simpleHello", "world");
        let err_buf = Vec::new();
        let err_buf = key.set_st(YDB_NOTTP, err_buf, "data").unwrap();
        key[0].clear();

        let err = key.get_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, YDB_ERR_LVUNDEF);

        let err_buf = key.node_next_self_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(&key[0], b"world");
        assert_eq!(&key.get_st(YDB_NOTTP, err_buf).unwrap(), b"data");
    }

    // https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-codes
    // NOTE: if one of these tests fails, you can use
    // `RUST_BACKTRACE=1 cargo test --lib common_errors` to find out which.
    #[test]
    fn common_errors() {
        let expect_err_with = |key: Key, err_code, get| {
            // data_st
            let err = key.data_st(YDB_NOTTP, Vec::with_capacity(50)).unwrap_err();
            assert_eq!(err.status, err_code);

            // delete_st
            let err =
                key.delete_st(YDB_NOTTP, Vec::with_capacity(50), DeleteType::DelNode).unwrap_err();
            assert_eq!(err.status, err_code);

            // incr_st
            let err = key.incr_st(YDB_NOTTP, Vec::with_capacity(50), None).unwrap_err();
            assert_eq!(err.status, err_code);

            // get_st
            if get {
                let err = key.get_st(YDB_NOTTP, Vec::with_capacity(50)).unwrap_err();
                assert_eq!(err.status, err_code);

                let err = key.set_st(YDB_NOTTP, Vec::with_capacity(50), b"some val").unwrap_err();
                assert_eq!(err.status, err_code);
            }

            // lock_st
            let slice = std::slice::from_ref(&key);
            let res = lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(0), slice);
            assert_eq!(res.unwrap_err().status, err_code);

            // lock_incr_st
            let err = key.lock_incr_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1)).unwrap_err();
            assert_eq!(err.status, err_code);

            // lock_decr_st
            let err = key.lock_decr_st(YDB_NOTTP, Vec::new()).unwrap_err();
            assert_eq!(err.status, err_code);

            // node_next_st
            let mut dup = key.clone();
            let err = dup.node_next_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
            assert_eq!(err.status, err_code);

            // node_prev_st
            let mut dup = key.clone();
            let err = dup.node_prev_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
            assert_eq!(err.status, err_code);

            // sub_next_st
            let mut dup = key.clone();
            let err = dup.sub_next_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
            assert_eq!(err.status, err_code);

            // sub_prev_st
            let mut dup = key.clone();
            let err = dup.sub_prev_self_st(YDB_NOTTP, Vec::new()).unwrap_err();
            assert_eq!(err.status, err_code);
        };
        let expect_err = |varname, err_code, get| {
            expect_err_with(Key::variable(varname), err_code, get);
        };
        expect_err("^", craw::YDB_ERR_INVVARNAME, true);
        expect_err("1", craw::YDB_ERR_INVVARNAME, true);
        expect_err("a_b_c", craw::YDB_ERR_INVVARNAME, true);
        expect_err("$ZCHSET", craw::YDB_ERR_UNIMPLOP, false);
        expect_err("$NOTANINTRINSIC", craw::YDB_ERR_INVSVN, true);
        expect_err(
            "^ThisIsAVeryLongVariableNameWithFarTooManyLetters",
            craw::YDB_ERR_VARNAME2LONG,
            true,
        );

        let subscripts: Vec<_> = (1..100).map(|i| i.to_string().into_bytes()).collect();
        let too_many_subscripts = Key::new("^somevar", &subscripts);
        expect_err_with(too_many_subscripts, craw::YDB_ERR_MAXNRSUBSCRIPTS, true);
    }

    #[test]
    fn increment_errors() {
        let key = Key::variable("incrementError");
        let err_buf = Vec::with_capacity(50);
        let err_buf = key.set_st(YDB_NOTTP, err_buf, "9E46").unwrap();
        let err = key.incr_st(YDB_NOTTP, err_buf, Some(b"1E46")).unwrap_err();
        assert_eq!(err.status, crate::craw::YDB_ERR_NUMOFLOW);
    }
    #[test]
    fn undef_var() {
        use crate::craw::{YDB_ERR_GVUNDEF, YDB_ERR_LVUNDEF};
        let key = Key::variable("^doesnotexist");
        let err_buf = Vec::with_capacity(10);
        let res = key.get_st(YDB_NOTTP, err_buf);
        assert_eq!(res.unwrap_err().status, YDB_ERR_GVUNDEF);

        let key = Key::variable("doesnotexist");
        let err_buf = Vec::with_capacity(10);
        let res = key.get_st(YDB_NOTTP, err_buf);
        assert_eq!(res.unwrap_err().status, YDB_ERR_LVUNDEF);
    }

    #[test]
    fn release() {
        let version = dbg!(release_t(YDB_NOTTP, Vec::new()).unwrap());
        let mut parts = version.split_whitespace();
        assert_eq!(parts.next(), Some("rustwr"));
        assert_eq!(parts.next(), Some(env!("CARGO_PKG_VERSION")));
        assert_eq!(parts.next(), Some("YottaDB"));
        assert_eq!(&parts.next().unwrap()[0..1], "r");
        assert_eq!(parts.count(), 2);
    }
}
