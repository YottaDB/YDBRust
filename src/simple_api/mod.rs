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
use std::cmp::min;
use std::fmt;
use std::error;
use std::panic;
use crate::craw::{ydb_buffer_t, ydb_get_st, ydb_set_st, ydb_data_st, ydb_delete_st, ydb_message_t,
    ydb_incr_st, ydb_node_next_st, ydb_node_previous_st, ydb_subscript_next_st, ydb_subscript_previous_st,
    ydb_tp_st, YDB_OK,
    YDB_ERR_INVSTRLEN, YDB_ERR_INSUFFSUBS, YDB_DEL_TREE, YDB_DEL_NODE, YDB_TP_ROLLBACK};

const DEFAULT_CAPACITY: usize = 1024;

#[derive(Clone, Hash, Eq, PartialEq)]
pub struct YDBError {
    pub message: Vec<u8>,
    pub status: i32,
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
        let mut out_buffer_t = Key::make_out_buffer_t(&mut out_buffer);
        let mut err_str = out_buffer_t;
        let ret_code = unsafe {
            ydb_message_t(self.tptoken, &mut err_str, self.status, &mut out_buffer_t)
        };
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        if ret_code != YDB_OK as i32 {
            unsafe {
                out_buffer.set_len(min(err_str.len_used, out_buffer_t.len_alloc) as usize);
            }
        } else {
            unsafe {
                out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
            }
        }
        let message = if ret_code != YDB_OK as i32 {
            std::borrow::Cow::from(format!("<error retrieving error message: {}>", ret_code))
        } else {
            String::from_utf8_lossy(&out_buffer)
        };
        write!(f, "YDB Error ({}): {}", message, String::from_utf8_lossy(&self.message))
    }
}

impl error::Error for YDBError {
    fn cause(&self) -> Option<&dyn error::Error> {
        Some(self)
    }
}

pub type YDBResult<T> = Result<T, YDBError>;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum DataReturn {
    NoData,
    ValueData,
    TreeData,
    ValueTreeData,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum DeleteType {
    DelNode,
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

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct Key {
    buffers: Vec<Vec<u8>>,
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
        // TODO: check if the variable is valid
        let variable = variable.into();
        Key {
            // NOTE: we cannot remove this copy because `node_next_st` mutates subscripts
            // and `node_subscript_st` mutates the variable
            buffers: std::iter::once(variable.into_bytes())
                .chain(subscripts.iter().cloned().map(|slice| slice.into()))
                .collect(),
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
    pub fn get_st(&self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let mut err_buffer_t = out_buffer_t;

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let status = unsafe {
            ydb_get_st(tptoken, &mut err_buffer_t, varname.as_ptr(), (self.buffers.len() - 1) as i32,
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
    pub fn set_st<U>(&self, tptoken: u64, mut out_buffer: Vec<u8>, new_val: U) -> YDBResult<Vec<u8>>
            where U: AsRef<[u8]> {
        let new_val = new_val.as_ref();
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let new_val_t = ydb_buffer_t {
            buf_addr: new_val.as_ptr() as *const _ as *mut _,
            len_alloc: new_val.len() as u32,
            len_used: new_val.len() as u32,
        };

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        // Do the call
        let status = unsafe {
            ydb_set_st(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                subscripts.as_ptr() as *const _, &new_val_t)
        };
        // Handle resizing the buffer, if needed
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.set_st(tptoken, out_buffer, &new_val);
        }
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
        let mut out_buffer = out_buffer;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let mut retval: u32 = 0;
        // Do the call
        let status = unsafe {
            ydb_data_st(tptoken, &mut out_buffer_t, varname.as_ptr(), (self.buffers.len() - 1) as i32,
                subscripts.as_ptr() as *const _, &mut retval as *mut _)
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
        let mut out_buffer = out_buffer;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        // Do the call
        let status = unsafe {
            ydb_delete_st(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                subscripts.as_ptr() as *const _, match delete_type {
                    DeleteType::DelNode => YDB_DEL_NODE,
                    DeleteType::DelTree => YDB_DEL_TREE,
                } as i32)
        };
        // Handle resizing the buffer, if needed
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.delete_st(tptoken, out_buffer, delete_type);
        }
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
    pub fn incr_st(&self, tptoken: u64, out_buffer: Vec<u8>, increment: Option<&Vec<u8>>)
            -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let mut err_buffer_t = out_buffer_t;
        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let status: i32;
        // We have to duplicate some code here to ensure that increment_t won't drop
        // out of scope after we unwrap increment (i.e., if we used a match)
        // This only showed up in release testing.
        if let Some(increment_v) = increment {
            let increment_t = &mut ydb_buffer_t {
                buf_addr: increment_v.as_ptr() as *const _ as *mut _,
                len_alloc: increment_v.capacity() as u32,
                len_used: increment_v.len() as u32,
            };
            status = unsafe {
                ydb_incr_st(tptoken, &mut err_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                subscripts.as_ptr() as *const _, increment_t, &mut out_buffer_t)
            };
            // Handle resizing the buffer, if needed
            if status == YDB_ERR_INVSTRLEN {
                out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
                return self.incr_st(tptoken, out_buffer, increment);
            }
        } else {
            let increment_t = ptr::null_mut();
            // Do the call
            status = unsafe {
                ydb_incr_st(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                subscripts.as_ptr() as *const _, increment_t, &mut out_buffer_t)
            };
            // Handle resizing the buffer, if needed
            if status == YDB_ERR_INVSTRLEN {
                out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
                return self.incr_st(tptoken, out_buffer, increment);
            }
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
    ///     key[1] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, "Hello")?;
    ///     // Lose the subscript, or pretend we are starting at ""
    ///     unsafe {
    ///         key[1].set_len(0);
    ///     }
    ///     output_buffer = key.node_next_self_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&key[1], b"a");
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
    ///     key[1] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, "Hello")?;
    ///     // We need to start at node beyond the node we are looking for; just add some Z's
    ///     key[1] = Vec::from("z");
    ///     output_buffer = key.node_prev_self_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(key[1], b"b");
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
        let len = (self.buffers.len() - 1) as i32;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // this is a loop instead of a recursive call so we can keep the original `len`
        let (ret_subs_used, buffer_structs) = loop {
            // Get pointers to the varname and to the first subscript
            let (varname, mut subscripts) = self.get_buffers_mut();
            assert!(!subscripts.is_empty());
            assert_eq!(subscripts.len(), self.buffers.len() - 1);
            let mut ret_subs_used = subscripts.len() as i32;

            // Do the call
            let status = unsafe {
                c_func(tptoken, &mut out_buffer_t, &varname, len,
                    subscripts.as_ptr(), &mut ret_subs_used as *mut _, subscripts.as_mut_ptr())
            };
            let ret_subs_used = (ret_subs_used + 1) as usize;
            // Handle resizing the buffer, if needed
            if status == YDB_ERR_INVSTRLEN {
                let last_sub_index = ret_subs_used;
                assert!(last_sub_index < self.buffers.len());

                let t = &mut self.buffers[last_sub_index];
                let needed_size = subscripts[last_sub_index - 1].len_used as usize;
                t.reserve(needed_size - t.len());
                assert_ne!(t.as_ptr(), std::ptr::null());

                continue;
            }
            if status == YDB_ERR_INSUFFSUBS {
                self.buffers.resize_with(ret_subs_used, || Vec::with_capacity(10));
                continue;
            }
            if status == crate::craw::YDB_ERR_PARAMINVALID {
                let i = ret_subs_used - 1;
                panic!("internal error in node_prev_st: buffer_structs[{}] was null: {:?}", i, subscripts[i]);
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
            subscripts.insert(0, varname);
            break (ret_subs_used, subscripts);
        };
        assert!(ret_subs_used <= self.buffers.len(),
            "growing the buffer should be handled in YDB_ERR_INSUFFSUBS (ydb {} > actual {})",
            ret_subs_used, self.buffers.len());
        self.buffers.truncate(ret_subs_used);

        for (i, buff) in self.buffers.iter_mut().enumerate() {
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
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloSubNext", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     key[1] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     // Start at a, next subscript will be b
    ///     key[1] = Vec::from("a");
    ///     output_buffer = key.sub_next_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&output_buffer, b"b");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn sub_next_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let status = unsafe {
            ydb_subscript_next_st(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                subscripts.as_ptr() as *const _, &mut out_buffer_t)
        };
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.sub_next_st(tptoken, out_buffer);
        }
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
    ///     key[1] = Vec::from("b");
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
        let mut out_buffer = out_buffer;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let status = unsafe {
            ydb_subscript_previous_st(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                subscripts.as_ptr() as *const _, &mut out_buffer_t)
        };
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.sub_prev_st(tptoken, out_buffer);
        }
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloSubNextSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     key[1] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     // Starting at a, the next sub should be b
    ///     key[1] = Vec::from("a");
    ///     output_buffer = key.sub_next_self_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&key[1], b"b");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn sub_next_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let mut last_self_buffer = {
            let t = self.buffers.last_mut().unwrap();
            ydb_buffer_t {
                buf_addr: t.as_mut_ptr() as *mut _,
                len_alloc: t.capacity() as u32,
                len_used: t.len() as u32,
            }
        };

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let status = unsafe {
            ydb_subscript_next_st(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                subscripts.as_ptr() as *const _, &mut last_self_buffer)
        };
        if status == YDB_ERR_INVSTRLEN {
            let t = self.buffers.last_mut().unwrap();
            // New size should be size needed + (current size - len used)
            let new_size = (last_self_buffer.len_used - last_self_buffer.len_alloc) as usize;
            let new_size = new_size + (t.capacity() - t.len());
            t.reserve(new_size);
            return self.sub_next_self_st(tptoken, out_buffer);
        }
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
            self.buffers.last_mut().unwrap()
                .set_len(min(last_self_buffer.len_alloc, last_self_buffer.len_used) as usize);
        }
        Ok(out_buffer)
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
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::{Key, YDBResult};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let mut key = make_key!("^helloSubPrevSelf", "a");
    ///     let mut output_buffer = Vec::with_capacity(1024);
    ///
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     key[1] = Vec::from("b");
    ///     output_buffer = key.set_st(YDB_NOTTP, output_buffer, b"Hello")?;
    ///     // Starting at b, previous should be a
    ///     output_buffer = key.sub_prev_self_st(YDB_NOTTP, output_buffer)?;
    ///
    ///     assert_eq!(&key[1], b"a");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn sub_prev_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let mut last_self_buffer = {
            let t = self.buffers.last_mut().unwrap();
            ydb_buffer_t {
                buf_addr: t.as_mut_ptr() as *mut _,
                len_alloc: t.capacity() as u32,
                len_used: t.len() as u32,
            }
        };

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_buffers();
        let status = unsafe {
            ydb_subscript_previous_st(tptoken, &mut out_buffer_t, varname.as_ptr(), subscripts.len() as i32,
                subscripts.as_ptr() as *const _, &mut last_self_buffer)
        };
        if status == YDB_ERR_INVSTRLEN {
            let t = self.buffers.last_mut().unwrap();
            // New size should be size needed + (current size - len used)
            let new_size = (last_self_buffer.len_used - last_self_buffer.len_alloc) as usize;
            let new_size = new_size + (t.capacity() - t.len());
            t.reserve(new_size);
            return self.sub_prev_self_st(tptoken, out_buffer);
        }
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
            self.buffers.last_mut().unwrap()
                .set_len(min(last_self_buffer.len_alloc, last_self_buffer.len_used) as usize);
        }
        Ok(out_buffer)
    }

    fn make_out_buffer_t(out_buffer: &mut Vec<u8>) -> ydb_buffer_t {
        ydb_buffer_t {
            buf_addr: out_buffer.as_mut_ptr() as *mut _,
            len_alloc: out_buffer.capacity() as u32,
            len_used: out_buffer.len() as u32,
        }
    }

    fn get_buffers_mut(&mut self) -> (ydb_buffer_t, Vec<ydb_buffer_t>) {
        let mut iter = self.buffers.iter_mut();
        // TODO: make varname its own field instead of part of `self.buffers`
        let var = Self::make_out_buffer_t(iter.next().unwrap());
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
        let make_buffer = |vec: &Vec<_>| ydb_buffer_t {
            // this cast is what's unsafe
            buf_addr: vec.as_ptr() as *mut _,
            len_alloc: vec.capacity() as u32,
            len_used: vec.len() as u32,
        }.into();
        let mut iter = self.buffers.iter();
        // TODO: make varname its own field instead of part of `self.buffers`
        let var = make_buffer(iter.next().unwrap());
        let subscripts = iter.map(make_buffer).collect();
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

/// Allow Key to mostly be treated as a `Vec<Vec<u8>>`,
/// but without `shrink_to_fit`, `drain`, or other methods that aren't relevant
impl Key {
    pub fn truncate(&mut self, i: usize) {
        self.buffers.truncate(i)
    }
    pub fn push(&mut self, subscript: Vec<u8>) {
        self.buffers.push(subscript)
    }
    pub fn pop(&mut self) -> Option<Vec<u8>> {
        self.buffers.pop()
    }
}

impl Deref for Key {
    type Target = Vec<Vec<u8>>;

    fn deref(&self) -> &Self::Target {
        &self.buffers
    }
}

impl Index<usize> for Key {
    type Output = Vec<u8>;

    fn index(&self, i: usize) -> &Self::Output {
        &self.buffers[i]
    }
}

impl IndexMut<usize> for Key {
    fn index_mut(&mut self, i: usize) -> &mut Vec<u8> {
        &mut self.buffers[i]
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

#[cfg(test)]
mod tests {
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
        result = key.set_st(0, result, &Vec::from("Hello world!")).unwrap();
        // Then try getting the value we set
        result = match key.get_st(0, result) {
            Ok(x) => x,
            Err(x) => {
                panic!("YDB Error: {}", x);
            }
        };
        assert_eq!(result, Vec::from("Hello world!"));
    }

    #[test]
    fn empty_subscript() {
        let mut key = Key::variable("tmp");
        key.push(Vec::new());
        key.get_st(0, Vec::with_capacity(1)).unwrap_err();
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
        result = key.set_st(0, result, &Vec::from("Hello world!")).unwrap();
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
    fn ydb_incr_st() {
        let result = Vec::with_capacity(1);
        let key = Key::variable("^helloIncrementMe");
        key.incr_st(0, result, None).unwrap();
    }

    #[test]
    fn ydb_node_next_self_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeNext", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::from("hyrule");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::from("a");
        key.node_next_self_st(0, result).unwrap();
    }

    #[test]
    fn ydb_node_next_self_extra_node_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeNext2", "worlds", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[2] = Vec::from("hyrule");
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
        key[1] = Vec::from("hyrule");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::from("z");
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
        key[2] = Vec::from("hyrule");
        result = key.set_st(0, result, &value).unwrap();
        key.truncate(2);
        key[1] = Vec::from("z");
        key.node_prev_self_st(0, result).unwrap();
    }

    #[test]
    fn ydb_subscript_next() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubNext", "a");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::with_capacity(1);
        result = key.sub_next_st(0, result).unwrap();
        assert_eq!(result, Vec::from("a"));
    }

    #[test]
    fn ydb_subscript_prev() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubprev", "b");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::from("z");
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
        key[1] = Vec::with_capacity(1);
        key.sub_next_self_st(0, result).unwrap();
        assert_eq!(key[1], Vec::from("shire"));
    }

    #[test]
    fn ydb_subscript_prev_self() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubprev2", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::from("z");
        key.sub_prev_self_st(0, result).unwrap();
        assert_eq!(key[1], Vec::from("shire"));
    }

    #[test]
    fn ydb_tp_st() {
        use crate::craw;

        // success
        let result = Vec::with_capacity(1);
        let result = tp_st(0, result, |_| {
            Ok(())
        }, "BATCH", &Vec::new()).unwrap();

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
        }, "BATCH", &Vec::new()).unwrap_err();
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
        err.status = 10001;
        assert!(err.to_string().contains("%SYSTEM-E-ENO10001, Unknown error 10001"));
    }
}
