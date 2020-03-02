//! Provides a more-friendly Rust-interface to the YottaDB API than the
//! raw C API (craw).
//!
//! Most operations are encapsulated in methods on the [`Key`][key] struct, and generally
//! consume a Vec<u8> and return ``Result<Vec<u8>>``. The return Vec<u8> will either contain
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
use crate::craw::{ydb_buffer_t, ydb_get_st, ydb_set_st, ydb_data_st, ydb_delete_st, ydb_message_t,
    ydb_incr_st, ydb_node_next_st, ydb_node_previous_st, ydb_subscript_next_st, ydb_subscript_previous_st,
    ydb_tp_st, YDB_OK,
    YDB_ERR_INVSTRLEN, YDB_ERR_INSUFFSUBS, YDB_DEL_TREE, YDB_DEL_NODE, YDB_TP_ROLLBACK};

const DEFAULT_CAPACITY: usize = 50;

/// An error returned by the underlying YottaDB library.
///
/// This error should not be constructed manually.
#[derive(Clone, Hash, Eq, PartialEq)]
pub struct YDBError {
    /// YottaDB internally uses an error-handling mechanism similar to `errno` and `perror`.
    /// Since, in a threaded context, another error may occur before the application has
    /// a chance to call `perror()` (in YottaDB, `$ZSTATUS`),
    /// the stringified error must be returned at the same time as the status code.
    pub message: Vec<u8>,
    /// The status returned by a YottaDB function. This will be a `YDB_ERR_*` constant.
    pub status: i32,
    /// The transaction that was in process when the error occurred.
    pub tptoken: u64
}

impl fmt::Debug for YDBError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "YDB Error ({}): {}", self.status, String::from_utf8_lossy(&self.message))
    }
}

impl fmt::Display for YDBError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut out_buffer = Vec::with_capacity(DEFAULT_CAPACITY);
        let message = loop {
            let mut out_buffer_t = Key::make_out_buffer_t(&mut out_buffer);
            let mut err_str = out_buffer_t;
            let ret_code = unsafe {
                ydb_message_t(self.tptoken, &mut err_str, self.status, &mut out_buffer_t)
            };
            // Resize the vec with the buffer to we can see the value
            // We could end up with a buffer of a larger size if we couldn't fit the error string
            // into the out_buffer, so make sure to pick the smaller size
            if ret_code == YDB_ERR_INVSTRLEN {
                out_buffer.resize(out_buffer_t.len_used as usize, Default::default());
                continue;
            } else if ret_code != YDB_OK as i32 {
                unsafe {
                    out_buffer.set_len(min(err_str.len_used, out_buffer_t.len_alloc) as usize);
                }
            } else {
                unsafe {
                    out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
                }
            }
            break if ret_code != YDB_OK as i32 {
                std::borrow::Cow::from(format!("<error retrieving error message: {}>", ret_code))
            } else {
                String::from_utf8_lossy(&out_buffer)
            }
        };
        write!(f, "YDB Error ({}): {}", message, String::from_utf8_lossy(&self.message))
    }
}

impl error::Error for YDBError {
    fn cause(&self) -> Option<&dyn error::Error> {
        Some(self)
    }
}

/// A specialized `Result` type returned by a YottaDB function.
pub type YDBResult<T> = Result<T, YDBError>;

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
    /// This is being [tracked upstream][from-arr-issue] and will hopefully be fixed soon.
    ///
    /// [vars]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#variables-vs-subscripts-vs-values
    /// [from-arr-issue]: https://github.com/rust-lang/rust/issues/67963
    pub fn new<V, S>(variable: V, subscripts: &[S]) -> Key
            where V: Into<String>,
                  S: Into<Vec<u8>> + Clone, {
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^hello");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, "Hello world!")?;
    ///     output_buffer = key.get_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&output_buffer, b"Hello world!");
    ///
    ///     Ok(())
    /// }
    /// ```
    // get_st can't use non_allocating call since it needs to distinguish between `out_buffer_t` and `err_buffer_t`
    pub fn get_st(&self, tptoken: u64, mut out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let mut err_buffer_t = out_buffer_t;

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let status = unsafe {
            ydb_get_st(tptoken, &mut err_buffer_t, varname.as_ptr(), self.subscripts.len() as i32,
                subscripts.as_ptr() as *const _, &mut out_buffer_t)
        };
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.get_st(tptoken, out_buffer);
        }
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        if status != YDB_OK as i32 {
            unsafe {
                out_buffer.set_len(min(err_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
            }
            return Err(YDBError { message: out_buffer, status, tptoken });
        }
        unsafe {
            out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
        }
        Ok(out_buffer)
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^hello");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     key.set_st(YDB_NOTTP, output_buffer, b"Hello world!")?;
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn set_st<U>(&self, tptoken: u64, out_buffer: Vec<u8>, new_val: U) -> YDBResult<Vec<u8>>
            where U: AsRef<[u8]> {
        let new_val = new_val.as_ref();
        let new_val_t = ydb_buffer_t {
            buf_addr: new_val.as_ptr() as *const _ as *mut _,
            len_alloc: new_val.len() as u32,
            len_used: new_val.len() as u32,
        };
        let do_call = |tptoken, out_buffer_p, varname_p, len, subscripts_p| {
            unsafe { ydb_set_st(tptoken, out_buffer_p, varname_p, len, subscripts_p, &new_val_t) }
        };
        self.non_allocating_call(tptoken, out_buffer, do_call)
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult, DataReturn};
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^helloValueDoesntExist");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     let (output, output_buffer) = key.data_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(DataReturn::NoData, output);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn data_st(&self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<(DataReturn, Vec<u8>)> {
        let mut retval: u32 = 0;
        let do_call = |tptoken, out_buffer_p, varname_p, len, subscripts_p| {
            unsafe { ydb_data_st(tptoken, out_buffer_p, varname_p, len, subscripts_p, &mut retval as *mut _) }
        };
        let out_buffer = self.non_allocating_call(tptoken, out_buffer, do_call)?;
        Ok((match retval {
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
                String::from_utf8_lossy(&out_buffer)),
        }, out_buffer))
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult, DeleteType};
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^hello");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.delete_st(YDB_NOTTP, output_buffer, DeleteType::DelTree)?;
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn delete_st(&self, tptoken: u64, out_buffer: Vec<u8>, delete_type: DeleteType)
            -> YDBResult<Vec<u8>> {
        let c_delete_ty = match delete_type {
            DeleteType::DelNode => YDB_DEL_NODE,
            DeleteType::DelTree => YDB_DEL_TREE,
        } as i32;
        self.non_allocating_call(tptoken, out_buffer, |tptoken, out_buffer_p, varname_p, len, subscripts_p| {
            unsafe { ydb_delete_st(tptoken, out_buffer_p, varname_p, len, subscripts_p, c_delete_ty) }
        })
    }

    // A call that can reallocate the `out_buffer`, but cannot modify `self`.
    //
    // `non_allocating_call` assumes that there are no extant references to `out_buffer`.
    // Functions that require a separate `err_buffer_t` cannot use `non_allocating_call`.
    //
    // `non_allocating_call` assumes that on error, `func` should be called again.
    // Functions which require `func` to only be called once cannot use `non_allocating_call`.
    fn non_allocating_call<F>(&self, tptoken: u64, mut out_buffer: Vec<u8>, mut func: F) -> YDBResult<Vec<u8>>
    where F: FnMut(u64, *mut ydb_buffer_t, *const ydb_buffer_t, i32, *const ydb_buffer_t) -> c_int {
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();

        let status = loop {
            // Do the call
            let status = func(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32, subscripts.as_ptr() as *const _);
            // Handle resizing the buffer, if needed
            if status == YDB_ERR_INVSTRLEN {
                out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
                continue;
            }
            break status;
        };
        // Set length of the vec containing the buffer to we can see the value
        if status != YDB_OK as i32 {
            // We could end up with a buffer of a larger size if we couldn't fit the error string
            // into the out_buffer, so make sure to pick the smaller size
            unsafe {
                out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
            }
            return Err(YDBError { message: out_buffer, status, tptoken });
        }
        Ok(out_buffer)
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
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloIncrementDocTest");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, "0")?;
    ///     output_buffer = key.get_st(YDB_NOTTP, output_buffer)?;
    ///     let before: i32 = String::from_utf8_lossy(&output_buffer).parse()?;
    ///     output_buffer = key.incr_st(YDB_NOTTP, output_buffer, None)?;
    ///     let now: i32  = String::from_utf8_lossy(&output_buffer).parse()?;
    ///     output_buffer = key.get_st(YDB_NOTTP, output_buffer)?;
    ///     let after: i32 = String::from_utf8_lossy(&output_buffer).parse()?;
    ///
    ///     assert!(before < now);
    ///     assert!(before + 1 == now);
    ///     assert!(after == now);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn incr_st(&self, tptoken: u64, mut out_buffer: Vec<u8>, increment: Option<&[u8]>)
            -> YDBResult<Vec<u8>> {
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let mut err_buffer_t = out_buffer_t;
        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let status: i32;
        let mut increment_t_buf;
        let increment_t = if let Some(increment_v) = increment {
            increment_t_buf = ydb_buffer_t {
                buf_addr: increment_v.as_ptr() as *const _ as *mut _,
                len_alloc: increment_v.len() as u32,
                len_used: increment_v.len() as u32,
            };
            &mut increment_t_buf as *mut _
        } else {
            ptr::null_mut()
        };
        status = unsafe {
            ydb_incr_st(tptoken, &mut err_buffer_t, varname.as_ptr(), subscripts.len() as i32,
            subscripts.as_ptr() as *const _, increment_t, &mut out_buffer_t)
        };
        // Handle resizing the buffer, if needed
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.get_st(tptoken, out_buffer);
        }
        // Set length of the vec containing the buffer to we can see the value
        if status != YDB_OK as i32 {
            unsafe {
                out_buffer.set_len(min(err_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
            }
            // We could end up with a buffer of a larger size if we couldn't fit the error string
            // into the out_buffer, so make sure to pick the smaller size
            return Err(YDBError { message: out_buffer, status, tptoken });
        }
        let new_buffer_size = min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize;
        unsafe {
            out_buffer.set_len(new_buffer_size);
        }
        Ok(out_buffer)
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
    /// use yottadb::YDB_NOTTP;
    /// use yottadb::simple_api::Key;
    /// use std::time::Duration;
    ///
    /// let key = Key::variable("lockDecrStTest");
    /// key.lock_incr_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1))?;
    /// key.lock_decr_st(YDB_NOTTP, Vec::new())?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # See also
    /// - The C [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-lock-decr-s-ydb-lock-decr-st)
    /// - [Locks](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#locks)
    /// - [Variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#variables-vs-subscripts-vs-values)
    pub fn lock_decr_st(&self, tptoken: u64, mut out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        use crate::craw::ydb_lock_decr_st;

        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let (var, subscripts) = self.get_buffers();
        let status = unsafe {
            ydb_lock_decr_st(tptoken, &mut out_buffer_t, var.as_ptr(), subscripts.len() as c_int, subscripts.as_ptr() as *const _)
        };

        let len = min(out_buffer_t.len_used, out_buffer_t.len_alloc);
        unsafe {
            out_buffer.set_len(len as usize);
        }
        if status != YDB_OK as c_int {
            Err(YDBError { message: out_buffer, status, tptoken })
        } else {
            Ok(out_buffer)
        }
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
    /// use yottadb::YDB_NOTTP;
    /// use yottadb::simple_api::Key;
    /// use std::time::Duration;
    ///
    /// let key = Key::variable("lockIncrStTest");
    /// key.lock_incr_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1))?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # See also
    /// - The C [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-lock-decr-s-ydb-lock-decr-st)
    /// - [Locks](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#locks)
    /// - [Variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#variables-vs-subscripts-vs-values)
    pub fn lock_incr_st(&self, tptoken: u64, mut out_buffer: Vec<u8>, timeout: Duration) -> YDBResult<Vec<u8>> {
        use std::convert::TryInto;
        use crate::craw::{ydb_lock_incr_st, YDB_ERR_TIME2LONG};

        let timeout_ns = match timeout.as_nanos().try_into() {
            Err(_) => {
                // discard any previous error
                out_buffer.clear();
                return Err(YDBError {
                    status: YDB_ERR_TIME2LONG,
                    message: out_buffer,
                    tptoken,
                });
            }
            Ok(n) => n,
        };
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let (var, subscripts) = self.get_buffers();
        let status = unsafe {
            ydb_lock_incr_st(tptoken, &mut out_buffer_t, timeout_ns, var.as_ptr(), subscripts.len() as c_int, subscripts.as_ptr() as *const _)
        };

        let len = min(out_buffer_t.len_used, out_buffer_t.len_alloc);
        unsafe {
            out_buffer.set_len(len as usize);
        }
        if status != YDB_OK as c_int {
            Err(YDBError { message: out_buffer, status, tptoken })
        } else {
            Ok(out_buffer)
        }
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloNodeNextSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, "Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, "Hello")?;
    ///     // Lose the subscript, or pretend we are starting at ""
    ///     key[0].clear();
    ///     output_buffer = key.node_next_self_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&key[0], b"a");
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// [how-it-works]: https://yottadb.com/product/how-it-works/
    /// [vars-nodes]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#keys-values-nodes-variables-and-subscripts
    pub fn node_next_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloNodePrevSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, "Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, "Hello")?;
    ///     // We need to start at node beyond the node we are looking for; just add some Z's
    ///     key[0] = Vec::from("z");
    ///     output_buffer = key.node_prev_self_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(key[0], b"b");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn node_prev_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.growing_shrinking_call(tptoken, out_buffer, ydb_node_previous_st)
    }
    fn growing_shrinking_call(&mut self, tptoken: u64, mut out_buffer: Vec<u8>,
        c_func: unsafe extern "C" fn(u64, *mut ydb_buffer_t, *const ydb_buffer_t, c_int, *const ydb_buffer_t, *mut c_int, *mut ydb_buffer_t) -> c_int
    ) -> YDBResult<Vec<u8>> {
        let len = self.subscripts.len() as i32;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

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
                c_func(tptoken, &mut out_buffer_t, &varname, len,
                    subscripts.as_ptr(), &mut ret_subs_used as *mut _, subscripts.as_mut_ptr())
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
                panic!("internal error in node_prev_st: subscripts[{}] was null: {:?}", i, subscripts[i]);
            }
            // Set length of the vec containing the buffer to we can see the value
            if status != YDB_OK as i32 {
                // We could end up with a buffer of a larger size if we couldn't fit the error string
                // into the out_buffer buffer, so make sure to pick the smaller size
                let new_buffer_size = min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize;
                unsafe {
                    out_buffer.set_len(new_buffer_size);
                }
                return Err(YDBError { message: out_buffer, status, tptoken });
            }
            break (ret_subs_used, subscripts);
        };
        assert!(ret_subs_used <= self.subscripts.len(),
            "growing the buffer should be handled in YDB_ERR_INSUFFSUBS (ydb {} > actual {})",
            ret_subs_used, self.subscripts.len());
        self.subscripts.truncate(ret_subs_used);

        for (i, buff) in self.subscripts.iter_mut().enumerate() {
            let actual = buffer_structs[i].len_used as usize;
            unsafe {
                buff.set_len(actual);
            }
        }

        Ok(out_buffer)
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let mut key = make_key!("^helloSubNext", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     // Start at a, next subscript will be b
    ///     key[0] = Vec::from("a");
    ///     output_buffer = key.sub_next_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&output_buffer, b"b");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn sub_next_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.sub_call(tptoken, out_buffer, ydb_subscript_next_st)
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloSubPrev", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     // Starting at b, the previous subscript should be a
    ///     output_buffer = key.sub_prev_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&output_buffer, b"a");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn sub_prev_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.sub_call(tptoken, out_buffer, ydb_subscript_previous_st)
    }

    // `sub_prev` and `sub_next` use the same memory allocation logic.
    fn sub_call(&mut self, tptoken: u64, mut out_buffer: Vec<u8>,
        func: unsafe extern "C" fn(u64, *mut ydb_buffer_t, *const ydb_buffer_t, i32, *const ydb_buffer_t, *mut ydb_buffer_t) -> c_int
    ) -> YDBResult<Vec<u8>> {
        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        let status = loop {
            let status = unsafe {
                func(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                    subscripts.as_ptr() as *const _, &mut out_buffer_t)
            };
            if status == YDB_ERR_INVSTRLEN {
                out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
                out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
                continue;
            }
            break status;
        };
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        let new_buffer_size = min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize;
        unsafe {
            out_buffer.set_len(new_buffer_size);
        }
        if status != YDB_OK as i32 {
            return Err(YDBError { message: out_buffer, status, tptoken });
        }
        Ok(out_buffer)
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
    /// use yottadb::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^helloSubNextSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     // Starting at a, the next sub should be b
    ///     key[0] = Vec::from("a");
    ///     output_buffer = key.sub_next_self_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&key[0], b"b");
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// `sub_next_self_st` can be written (less efficiently) using only safe code:
    /// ```
    /// use yottadb::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// # fn main() -> YDBResult<()> {
    ///
    /// // set up a node with data at `subNextSelfUser("b")`
    /// let mut user = Key::new("subNextSelfUser", &["b"]);
    /// user.set_st(YDB_NOTTP, Vec::new(), b"Hello")?;
    ///
    /// user[0] = "a".into();
    /// user[0] = user.sub_next_st(YDB_NOTTP, Vec::new())?;
    ///
    /// let mut ydb = Key::new("subNextSelfUser", &["a"]);
    /// ydb.sub_next_self_st(YDB_NOTTP, Vec::new())?;
    ///
    /// assert_eq!(user[0], ydb[0]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn sub_next_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
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
    /// use yottadb::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> YDBResult<()> {
    ///     let mut key = make_key!("^helloSubPrevSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     key[0] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     // Starting at b, previous should be a
    ///     output_buffer = key.sub_prev_self_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&key[0], b"a");
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// `sub_prev_self_st` can be written (less efficiently) using only safe code:
    /// ```
    /// use yottadb::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// # fn main() -> YDBResult<()> {
    ///
    /// // set up a node with data at `subPrevSelfUser("a")`
    /// let mut user = Key::new("subPrevSelfUser", &["a"]);
    /// user.set_st(YDB_NOTTP, Vec::new(), b"Hello")?;
    ///
    /// user[0] = "b".into();
    /// user[0] = user.sub_prev_st(YDB_NOTTP, Vec::new()).unwrap();
    ///
    /// let mut ydb = Key::new("subPrevSelfUser", &["b"]);
    /// ydb.sub_prev_self_st(YDB_NOTTP, Vec::new())?;
    ///
    /// assert_eq!(user[0], ydb[0]);
    /// # Ok(())
    /// # }
    pub fn sub_prev_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        self.sub_self_call(tptoken, out_buffer, ydb_subscript_previous_st)
    }

    // `sub_prev_self` and `sub_next_self` use the same memory allocation logic.
    fn sub_self_call(&mut self, tptoken: u64, mut out_buffer: Vec<u8>,
        func: unsafe extern "C" fn(u64, *mut ydb_buffer_t, *const ydb_buffer_t, i32, *const ydb_buffer_t, *mut ydb_buffer_t) -> c_int
    ) -> YDBResult<Vec<u8>> {
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let t = self.subscripts.last_mut().unwrap_or(unsafe {
            self.variable.as_mut_vec()
        });
        let mut last_self_buffer;
        let status = loop {
            last_self_buffer = ydb_buffer_t {
                buf_addr: t.as_mut_ptr() as *mut _,
                len_alloc: t.capacity() as u32,
                len_used: t.len() as u32,
            };

            let status = unsafe {
                func(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                    subscripts.as_ptr() as *const _, &mut last_self_buffer)
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
                out_buffer.set_len(min(out_buffer_t.len_alloc, out_buffer_t.len_used) as usize);
            }
            return Err(YDBError { message: out_buffer, status, tptoken });
        }
        unsafe {
            t.set_len(min(last_self_buffer.len_alloc, last_self_buffer.len_used) as usize);
        }
        Ok(out_buffer)
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
        }.into();
        let make_buffer = |vec: &Vec<_>| ydb_buffer_t {
            // this cast is what's unsafe
            buf_addr: vec.as_ptr() as *mut _,
            len_alloc: vec.capacity() as u32,
            len_used: vec.len() as u32,
        }.into();
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

type UserResult = Result<(), Box<dyn Error>>;

enum CallBackError {
    // the callback returned an error
    ApplicationError(Box<dyn Error>),
    // the callback panicked; this is the value `panic!` was called with
    Panic(Box<dyn std::any::Any + Send + 'static>),
}
/// Passes the callback function as a structure to the callback
struct CallBackStruct<'a> {
    cb: &'a mut dyn FnMut(u64) -> UserResult,
    /// Application error (not a YDBError)
    error: Option<CallBackError>,
}

extern "C" fn fn_callback(tptoken: u64, errstr: *mut ydb_buffer_t,
                          tpfnparm: *mut c_void) -> i32 {
    assert!(!tpfnparm.is_null());
    assert!(!errstr.is_null());
    let callback_struct = unsafe { &mut *(tpfnparm as *mut CallBackStruct) };

    let mut cb = panic::AssertUnwindSafe(&mut callback_struct.cb);
    // this deref_mut() is because Rust is having trouble with type inferrence
    let retval = match panic::catch_unwind(move || cb.deref_mut()(tptoken)) {
        Ok(val) => val,
        Err(payload) => {
            callback_struct.error = Some(CallBackError::Panic(payload));
            return YDB_TP_ROLLBACK as i32;
        }
    };
    match retval {
        Ok(_) => YDB_OK as i32,
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
        },
    }
}

/// Start a new transaction, where `f` is the transaction to execute.
///
/// The parameter passed to `f` is a `tptoken`.
///
/// `f` must be `FnMut`, not `FnOnce`, since the YottaDB engine may
/// call f many times if necessary to ensure ACID properties.
/// This may affect your application logic; if you need to know how many
/// times the callback has been executed, get the [intrinsic variable][intrinsics]
/// [`$trestart`](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#trestart)
///
/// # See Also
/// - [More details about the underlying FFI call](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-tp-s-ydb-tp-st)
/// - [Transaction Processing in YottaDB](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing)
///
/// [intrinsics]: index.html#intrinsic-variables
pub fn tp_st<F>(tptoken: u64, mut out_buffer: Vec<u8>, mut f: F, trans_id: &str,
             locals_to_reset: &[Vec<u8>]) -> Result<Vec<u8>, Box<dyn Error>>
        where F: FnMut(u64) -> UserResult {
    let mut out_buffer_t = Key::make_out_buffer_t(&mut out_buffer);

    let mut locals = Vec::with_capacity(locals_to_reset.len());
    for local in locals_to_reset.iter() {
        locals.push(ydb_buffer_t {
            buf_addr: local.as_ptr() as *const _ as *mut _,
            len_alloc: local.capacity() as u32,
            len_used: local.len() as u32,
        });
    }
    let locals_ptr = match locals.len() {
        0 => ptr::null_mut(),
        _ => locals.as_mut_ptr(),
    };
    let c_str = CString::new(trans_id).unwrap();
    let mut callback_struct = CallBackStruct { cb: &mut f, error: None };
    let arg = &mut callback_struct as *mut _ as *mut c_void;
    let status = unsafe {
        ydb_tp_st(tptoken, &mut out_buffer_t, Some(fn_callback), arg, c_str.as_ptr(),
            locals.len() as i32, locals_ptr)
    };
    if status as u32 == YDB_OK {
        // from Steve:
        // > there may be a possibility for an error to occur that gets caught
        // > and handled which appear to use the buffer even though none was
        // > returned at a high level.
        unsafe {
            out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
        }
        Ok(out_buffer)
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
            out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
        }
        Err(Box::new(YDBError { message: out_buffer, status: status as i32, tptoken, }))
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
/// use yottadb::{YDB_NOTTP, YDB_ERR_LVUNDEF};
/// use yottadb::simple_api::{Key, delete_excl_st};
///
/// // Create three variables and set all
/// let a = Key::variable("deleteExclTestA");
/// a.set_st(YDB_NOTTP, Vec::new(), "test data")?;
/// let b = Key::variable("deleteExclTestB");
/// b.set_st(YDB_NOTTP, Vec::new(), "test data 2")?;
/// let c = Key::variable("deleteExclTestC");
/// c.set_st(YDB_NOTTP, Vec::new(), "test data 3")?;
///
/// // Delete all variables except `a`
/// delete_excl_st(YDB_NOTTP, Vec::new(), &[&a.variable])?;
/// assert_eq!(a.get_st(YDB_NOTTP, Vec::new())?, b"test data");
/// assert_eq!(b.get_st(YDB_NOTTP, Vec::new()).unwrap_err().status, YDB_ERR_LVUNDEF);
/// assert_eq!(c.get_st(YDB_NOTTP, Vec::new()).unwrap_err().status, YDB_ERR_LVUNDEF);
///
/// // Delete `a` too
/// delete_excl_st(YDB_NOTTP, Vec::new(), &[])?;
/// assert_eq!(a.get_st(YDB_NOTTP, Vec::new()).unwrap_err().status, YDB_ERR_LVUNDEF);
///
/// # Ok(())
/// # }
/// ```
///
/// # See also
/// - The [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-delete-excl-s-ydb-delete-excl-st)
/// - [Local and global variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#local-and-global-variables)
/// - [Instrinsic special variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#intrinsic-special-variables)
pub fn delete_excl_st(tptoken: u64, mut out_buffer: Vec<u8>, saved_variables: &[&str]) -> YDBResult<Vec<u8>> {
    use crate::craw::ydb_delete_excl_st;

    assert!(out_buffer.len() <= out_buffer.capacity());
    let mut out_buffer_t = Key::make_out_buffer_t(&mut out_buffer);

    let varnames: Vec<ConstYDBBuffer> = saved_variables.iter().map(|var| ydb_buffer_t {
        buf_addr: var.as_ptr() as *mut _,
        len_used: var.len() as u32,
        len_alloc: var.len() as u32,
    }.into()).collect();

    let status = unsafe {
        ydb_delete_excl_st(tptoken, &mut out_buffer_t, varnames.len() as c_int, varnames.as_ptr() as *const _)
    };

    let len = min(out_buffer_t.len_used, out_buffer_t.len_alloc);
    unsafe {
        out_buffer.set_len(len as usize);
    }
    if status != YDB_OK as c_int {
        Err(YDBError { message: out_buffer, status, tptoken })
    } else {
        Ok(out_buffer)
    }
}

/// Given a binary sequence, serialize it to 'Zwrite format', which is ASCII printable.
///
/// # Errors
/// - If YDB is in UTF8 mode, will return [`BADCHAR`] on invalid UTF8.
/// - Another [error code](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
///
/// # Examples
///
/// ```
/// # use yottadb::YDBError;
/// # fn main() -> Result<(), YDBError> {
/// use yottadb::simple_api::str2zwr_st;
/// use yottadb::YDB_NOTTP;
/// assert_eq!(str2zwr_st(YDB_NOTTP, Vec::new(), "💖".as_bytes())?, b"\"\xf0\"_$C(159,146,150)");
/// # Ok(())
/// # }
/// ```
///
/// # See also
/// - [Zwrite format](https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#zwrite-formatted)
/// - [`zwr2str_st`](fn.zwr2str_st.html), which deserializes a buffer in Zwrite format back to the original binary.
///
/// [`BADCHAR`]: https://docs.yottadb.com/MessageRecovery/errors.html#badchar
pub fn str2zwr_st(tptoken: u64, mut out_buf: Vec<u8>, original: &[u8]) -> YDBResult<Vec<u8>> {
    use crate::craw::ydb_str2zwr_st;

    let mut out_buffer_t = Key::make_out_buffer_t(&mut out_buf);
    let mut err_buffer_t = out_buffer_t;
    let original_t = ConstYDBBuffer::from(original);

    let status = unsafe {
        ydb_str2zwr_st(tptoken, &mut err_buffer_t, original_t.as_ptr(), &mut out_buffer_t)
    };

    if status == YDB_ERR_INVSTRLEN {
        let needed = out_buffer_t.len_used as usize;
        let current = out_buf.len();
        out_buf.reserve(needed - current);
        debug_assert!(needed <= out_buf.capacity());
        return str2zwr_st(tptoken, out_buf, original);
    }
    // Resize the vec with the buffer so we can see the value
    // We could end up with a buffer of a larger size if we couldn't fit the error string
    // into the out_buffer, so make sure to pick the smaller size
    let used = if status != YDB_OK as i32 {
        err_buffer_t.len_used
    } else {
        out_buffer_t.len_used
    };
    unsafe {
        out_buf.set_len(min(out_buffer_t.len_alloc, used) as usize);
    }
    assert!(out_buf.len() <= out_buf.capacity());
    if status != YDB_OK as i32 {
        Err(YDBError { message: out_buf, status, tptoken })
    } else {
        Ok(out_buf)
    }
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
/// use yottadb::YDB_NOTTP;
/// let out_buf = zwr2str_st(YDB_NOTTP, Vec::new(), b"\"\xf0\"_$C(159,146,150)")?;
/// assert_eq!(out_buf.as_slice(), "💖".as_bytes());
/// # Ok(())
/// # }
/// ```
///
/// # See also
/// - [Zwrite format](https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#zwrite-formatted)
/// - [str2zwr_st](fn.str2zwr_st.html), the inverse of `zwr2str_st`.
pub fn zwr2str_st(tptoken: u64, mut out_buf: Vec<u8>, serialized: &[u8]) -> Result<Vec<u8>, YDBError> {
    use crate::craw::ydb_zwr2str_st;

    let mut out_buffer_t = Key::make_out_buffer_t(&mut out_buf);
    let mut err_buffer_t = out_buffer_t;
    let serialized_t = ConstYDBBuffer::from(serialized);

    let status = unsafe {
        ydb_zwr2str_st(tptoken, &mut err_buffer_t, serialized_t.as_ptr(), &mut out_buffer_t)
    };

    if status == YDB_ERR_INVSTRLEN {
        out_buf.reserve(out_buffer_t.len_used as usize - out_buf.len());
        return zwr2str_st(tptoken, out_buf, serialized);
    } else if status == YDB_OK as c_int && out_buffer_t.len_used == 0 {
        out_buf.clear();
    }
    // Resize the vec with the buffer so we can see the value
    // We could end up with a buffer of a larger size if we couldn't fit the error string
    // into the out_buffer, so make sure to pick the smaller size
    let used = if status != YDB_OK as i32 {
        err_buffer_t.len_used
    } else {
        out_buffer_t.len_used
    };
    unsafe {
        out_buf.set_len(min(out_buffer_t.len_alloc, used) as usize);
    }
    if status != YDB_OK as i32 {
        Err(YDBError { message: out_buf, status, tptoken })
    } else {
        Ok(out_buf)
    }
}

/// Acquires locks specified in `locks` and releases all others.
///
/// This operation is atomic. If any lock cannot be acquired, no locks are acquired.
/// The `timeout` specifies the maximum time to wait before returning an error.
/// If no locks are specified, all locks are released.
///
/// Note that YottaDB locks are per-process, not per-thread.
///
/// # Errors
///
/// Possible errors for this function include:
/// - YDB_LOCK_TIMEOUT if all locks could not be acquired within the timeout period.
///   In this case, no locks are acquired.
/// - YDB_ERR_TIME2LONG if `timeout` is greater than `YDB_MAX_TIME_NSEC`
/// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
///
/// # Examples
/// ```
/// use std::time::Duration;
/// use yottadb::YDB_NOTTP;
/// use yottadb::simple_api::{Key, lock_st};
///
/// // acquire a new lock
/// let key = Key::variable("lockA");
/// lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &[&key]).unwrap();
///
/// // release all locks
/// lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &[]).unwrap();
/// ```
///
/// # See also
///
/// - The C [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-lock-s-ydb-lock-st)
/// - [Locks](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#locks)
/// - [`context_api::Context::lock`](../context_api/struct.Context.html#method.lock)
pub fn lock_st(tptoken: u64, mut out_buffer: Vec<u8>, timeout: Duration, locks: &[&Key]) -> YDBResult<Vec<u8>> {
    use crate::craw::{YDB_ERR_MAXARGCNT, MAXVPARMS, ydb_lock_st, ydb_call_variadic_plist_func, gparam_list};

    let mut err_buffer_t = Key::make_out_buffer_t(&mut out_buffer);
    let keys: Vec<_> = locks.iter().copied().map(Key::get_buffers).collect();

    // tptoken, err_buf, timeout, len, then each key is viewed by lock_st as 3 arguments
    let arg_count = 4 + keys.len() * 3;
    if arg_count > MAXVPARMS as usize {
        return Err(YDBError {
            status: YDB_ERR_MAXARGCNT,
            message: format!("Expected at most {} arguments, got {}", MAXVPARMS, arg_count).into_bytes(),
            tptoken,
        });
    }
    // setup the initial args. Note that all these arguments are required to have size uint64_t.
    let mut arg = [0; MAXVPARMS as usize];
    arg[0] = tptoken as usize;
    arg[1] = &mut err_buffer_t as *mut _ as usize;
    arg[2] = timeout.as_nanos() as usize;
    arg[3] = keys.len() as usize;

    for (i, (var, subscripts)) in keys.iter().enumerate() {
        // start at 4 since we've already used the first 4 slots
        arg[i + 4] = var.as_ptr() as usize;
        arg[i + 5] = subscripts.len() as usize;
        arg[i + 6] = subscripts.as_ptr() as usize;
    }
    let args = gparam_list { n: arg_count as isize, arg };
    let status = unsafe {
        // the types on `ydb_call_variadic_plist_func` are not correct
        // additionally, `ydb_lock_st` on its own is a unique zero-sized-type (ZST):
        // see https://doc.rust-lang.org/reference/types/function-item.html#function-item-types for more details on function types
        // and https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts for details on ZSTs.
        // this `as *const ()` turns the unique ZST for `ydb_lock_st` into a proper function pointer
        // without the `as` cast, `transmute` will return `1_usize` and `ydb_call` will subsequently segfault
        let ydb_lock_no_really_trust_me = std::mem::transmute(ydb_lock_st as *const ());
        ydb_call_variadic_plist_func(Some(ydb_lock_no_really_trust_me), &args as *const _ as usize)
    };

    // We could end up with a buffer of a larger size if we couldn't fit the error string
    // into the out_buffer, so make sure to pick the smaller size
    let len = min(err_buffer_t.len_used, err_buffer_t.len_alloc) as usize;
    unsafe { out_buffer.set_len(len); }

    if status != YDB_OK as c_int {
        Err(YDBError { message: out_buffer, status, tptoken })
    } else {
        Ok(out_buffer)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use serial_test::serial;

    use crate::*;
    use super::*;

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
        let key = Key::variable("^hello");

        // Try setting a value
        result = key.set_st(0, result, b"Hello world!").unwrap();
        // Then try getting the value we set
        result = key.get_st(0, result).unwrap();
        assert_eq!(result, Vec::from("Hello world!"));
    }

    #[test]
    fn ydb_get_st_error() {
        let result = Vec::with_capacity(1);
        let key = Key::variable("^helloDoesntExists");
        key.get_st(0, result).unwrap_err();
    }

    #[test]
    fn ydb_data_st() {
        let result = Vec::with_capacity(1);
        let key = Key::variable("^helloDoesNotExists");

        let (retval, _) = key.data_st(0, result).unwrap();
        assert_eq!(retval, DataReturn::NoData);
    }

    #[test]
    fn ydb_delete_st() {
        let mut result = Vec::with_capacity(1);
        let key = Key::variable("^helloDeleteMe");

        // Try setting a value
        result = key.set_st(0, result, b"Hello world!").unwrap();
        // Check data
        let (retval, mut result) = key.data_st(0, result).unwrap();
        assert_ne!(retval, DataReturn::NoData);
        // Delete the value
        result = key.delete_st(0, result, DeleteType::DelNode).unwrap();
        let (retval, _) = key.data_st(0, result).unwrap();
        // Check for no data
        assert_eq!(retval, DataReturn::NoData);
    }

    #[test]
    fn ydb_delete_excl_st() {
        let out_buf = Vec::new();
        let mut key = Key::variable("deleteExcl");

        // Set a few values
        let out_buf = key.set_st(0, out_buf, b"some value").unwrap();
        key.variable = "deleteExcl2".into();
        let out_buf = key.set_st(0, out_buf, b"some value").unwrap();

        // Delete `deleteExcl2`, saving `deleteExcl`
        let out_buf = delete_excl_st(0, out_buf, &["deleteExcl"]).unwrap();
        // Check data
        let (data_type, out_buf) = key.data_st(0, out_buf).unwrap();
        assert_eq!(data_type, DataReturn::NoData);
        key.variable = "deleteExcl".into();
        let (data_type, out_buf) = key.data_st(0, out_buf).unwrap();
        assert_eq!(data_type, DataReturn::ValueData);

        // Delete `deleteExcl`
        let out_buf = delete_excl_st(0, out_buf, &[]).unwrap();
        // Make sure it was actually deleted
        let (data_type, out_buf) = key.data_st(0, out_buf).unwrap();
        assert_eq!(data_type, DataReturn::NoData);

        // Saving a global/intrinsic variable should be an error
        use crate::craw::YDB_ERR_INVVARNAME;
        let err = delete_excl_st(0, out_buf, &["^global"]).unwrap_err();
        assert_eq!(err.status, YDB_ERR_INVVARNAME);
        let err = delete_excl_st(0, Vec::new(), &["$ZSTATUS"]).unwrap_err();
        assert_eq!(err.status, YDB_ERR_INVVARNAME);

        // Saving a variable that doesn't exist should do nothing and return YDB_OK.
        delete_excl_st(0, Vec::new(), &["local"]).unwrap();
    }

    #[test]
    fn ydb_incr_st() {
        let err_buf = Vec::with_capacity(1);
        let key = Key::variable("^helloIncrementMe");
        let err_buf = key.set_st(YDB_NOTTP, err_buf, "0").unwrap();

        let err_buf = key.incr_st(0, err_buf, Some(b"1500")).unwrap();
        assert_eq!(&key.get_st(YDB_NOTTP, err_buf).unwrap(), b"1500");
    }

    // Return the number of locks held for `var`
    pub(crate) fn lock_count(var: &str) -> usize {
        use std::os::raw::{c_char, c_ulong};
        use crate::craw::{ydb_ci_t, ydb_string_t};

        fn make_out_str_t(slice: &mut [u8]) -> ydb_string_t {
            ydb_string_t {
                address: slice.as_mut_ptr() as *mut c_char,
                length: slice.len() as c_ulong,
            }
        }

        std::env::set_var("ydb_routines", "examples/m-ffi");
        std::env::set_var("ydb_ci", "examples/m-ffi/zshvar.ci");

        let mut err_buf = Vec::new();

        let m_code = CString::new("zshvar").unwrap();
        let mut stored_var = Vec::from("outputvar");
        let mut output_var = Vec::from("l");
        let mut output_var_t = make_out_str_t(&mut output_var);
        let mut stored_var_t = make_out_str_t(&mut stored_var);
        let status = loop {
            let mut err_buf_t = Key::make_out_buffer_t(&mut err_buf);
            let status = unsafe {
                let func_ptr = m_code.as_ptr() as *const c_char;
                ydb_ci_t(YDB_NOTTP, &mut err_buf_t, func_ptr, &mut output_var_t as *mut _, &mut stored_var_t as *mut _)
            };
            if status == YDB_ERR_INVSTRLEN {
                err_buf.reserve(err_buf_t.len_used as usize - err_buf.len());
                continue;
            }
            break status;
        };
        assert_eq!(status, 0, "ydb_ci_t not successful: {}", YDBError { status, tptoken: YDB_NOTTP, message: err_buf });

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
                let count = &groups.next().unwrap()["LEVEL=".len()..];
                return count.parse().unwrap();
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
    }

    #[test]
    #[serial]
    fn ydb_lock_st() {
        // Test `ydb_lock`
        let key = Key::variable("ydbLock");
        assert_eq!(lock_count(&key.variable), 0);
        // Acquuire the lock
        lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &[&key]).unwrap();
        assert_eq!(lock_count(&key.variable), 1);
        // Release all locks
        lock_st(YDB_NOTTP, Vec::new(), Duration::from_secs(1), &[]).unwrap();
        assert_eq!(lock_count(&key.variable), 0);
    }

    #[test]
    fn ydb_node_next_self_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeNext", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[0] = Vec::from("hyrule");
        result = key.set_st(0, result, &value).unwrap();
        key[0] = Vec::from("a");
        key.node_next_self_st(0, result).unwrap();
    }

    #[test]
    fn ydb_node_next_self_extra_node_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeNext2", "worlds", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::from("hyrule");
        result = key.set_st(0, result, &value).unwrap();
        key.truncate(2);
        key.node_next_self_st(0, result).unwrap();
    }

    #[test]
    fn ydb_node_prev_self_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeprev", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[0] = Vec::from("hyrule");
        result = key.set_st(0, result, &value).unwrap();
        key[0] = Vec::from("z");
        if let Err(err) = key.node_prev_self_st(0, result) {
            panic!("{}", err);
        }
    }

    #[test]
    fn ydb_node_prev_self_extra_node_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeprev2", "worlds", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::from("hyrule");
        result = key.set_st(0, result, &value).unwrap();
        key.truncate(2);
        key[0] = Vec::from("z");
        key.node_prev_self_st(0, result).unwrap();
    }

    #[test]
    fn ydb_subscript_next() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubNext", "a");
        result = key.set_st(0, result, &value).unwrap();
        key[0] = Vec::with_capacity(1);
        result = key.sub_next_st(0, result).unwrap();
        assert_eq!(result, Vec::from("a"));
    }

    #[test]
    fn ydb_subscript_prev() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubprev", "b");
        result = key.set_st(0, result, &value).unwrap();
        key[0] = Vec::from("z");
        result = key.sub_prev_st(0, result).unwrap();
        assert_eq!(result, Vec::from("b"));
    }

    #[test]
    fn ydb_subscript_next_self() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubNext2", "shire");
        result = key.set_st(0, result, &value).unwrap();
        // TODO: we need a better way to expand these buffers in the _self function
        key[0] = Vec::with_capacity(1);
        key.sub_next_self_st(0, result).unwrap();
        assert_eq!(key[0], Vec::from("shire"));
    }

    #[test]
    fn ydb_subscript_prev_self() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubprev2", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[0] = Vec::from("z");
        key.sub_prev_self_st(0, result).unwrap();
        assert_eq!(key[0], Vec::from("shire"));
    }

    #[test]
    fn ydb_tp_st() {
        use crate::craw;

        // success
        let result = Vec::with_capacity(1);
        let result = tp_st(0, result, |_| {
            Ok(())
        }, "BATCH", &[]).unwrap();

        // user error
        let err = tp_st(0, result, |_| {
            Err("oops!".into())
        }, "BATCH", &[]).unwrap_err();
        assert_eq!(err.to_string(), "oops!");

        // ydb error
        let vec = Vec::with_capacity(10);
        let err = tp_st(0, vec, |tptoken| {
            let key = make_key!("hello");
            key.get_st(tptoken, Vec::with_capacity(1024))?;
            unreachable!();
        }, "BATCH", &[]).unwrap_err();
        assert!(err.downcast::<YDBError>().unwrap().status == craw::YDB_ERR_LVUNDEF);
    }

    #[test]
    #[should_panic]
    fn panic_in_cb() {
        tp_st(0, Vec::with_capacity(10), |_| panic!("oh no!"), "BATCH", &[]).unwrap_err();
    }

    #[test]
    fn ydb_message_t() {
        use crate::craw;
        let mut err = YDBError { message: Vec::new(), status: craw::YDB_ERR_GVUNDEF, tptoken: craw::YDB_NOTTP };
        assert!(err.to_string().contains("%YDB-E-GVUNDEF, Global variable undefined"));

        // make sure it works even if it has to resize the out_buffer
        err.status = 150380370;
        let expected = "%YDB-E-INVTRNSQUAL, Invalid TRANSACTION qualifier.  Specify only one of TRANSACTION=[NO]SET or TRANSACTION=[NO]KILL.";
        assert!(err.to_string().contains(expected), "expected INVTRNSQUAL, got {}", err.to_string());

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
        use crate::craw::{YDB_NOTTP, YDB_ERR_GVUNDEF};
        let key = Key::variable("^doesnotexist");
        let err_buf = Vec::new();
        let res = key.get_st(YDB_NOTTP, err_buf);
        assert_eq!(res.unwrap_err().status, YDB_ERR_GVUNDEF);
    }
    #[test]
    fn empty_subscript() {
        use crate::craw::{YDB_NOTTP, YDB_ERR_LVUNDEF};

        let mut key = make_key!("simpleHello", "world");
        let err_buf = Vec::new();
        let err_buf = key.set_st(YDB_NOTTP, err_buf, "data").unwrap();
        key[0].clear();

        let err = key.get_st(0, Vec::new()).unwrap_err();
        assert_eq!(err.status, YDB_ERR_LVUNDEF);

        let err_buf = key.node_next_self_st(YDB_NOTTP, err_buf).unwrap();
        assert_eq!(&key[0], b"world");
        assert_eq!(&key.get_st(YDB_NOTTP, err_buf).unwrap(), b"data");
    }
}
