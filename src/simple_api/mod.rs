//! Provides a Rust-interface to the YottaDB API in a more friendly manner than the
//! raw C API (craw).
//!
//! Most operations are encapusulated in methods on the Key struct, and generally
//! consume a Vec<u8> and return ``Result<Vec<u8>>``. The return Vec<u8> will contains
//! the data we were fetching from the database, or in the error case, an error.
//! The Vec<u8> may be resized as part of the call.
//!
//! # Examples
//!
//! A basic database operation (set a value, retrieve it, then delete it).
//!
//! ```no_run
//! # #[macro_use] extern crate yottadb;
//! use yottadb::craw::YDB_NOTTP;
//! use yottadb::simple_api::{Key, DeleteType};
//!
//! let mut key = make_key!("^MyGlobal", "SubscriptA", "42");
//! let mut buffer = Vec::with_capacity(1024);
//! let value = Vec::from("This is a persistent message");
//! buffer = match key.set_st(YDB_NOTTP, buffer, &value) {
//!     Ok(x) => x,
//!     Err(err) => panic!(err),
//! };
//! buffer = match key.get_st(YDB_NOTTP, buffer) {
//!     Ok(v) => v,
//!     Err(err) => panic!(err),
//! };
//! assert_eq!("This is a persistent message", String::from_utf8_lossy(&buffer));
//! key.delete_st(YDB_NOTTP, buffer, DeleteType::DelNode).unwrap();
//! ```
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::mem;
use std::ffi::CString;
use std::os::raw::c_void;
use std::cmp::min;
use std::fmt;
use std::error;
use crate::craw::{ydb_buffer_t, ydb_get_st, ydb_set_st, ydb_data_st, ydb_delete_st,
    ydb_incr_st, ydb_node_next_st, ydb_node_previous_st, ydb_subscript_next_st, ydb_subscript_previous_st,
    ydb_tp_st, YDB_OK,
    YDB_ERR_INVSTRLEN, YDB_ERR_INSUFFSUBS, YDB_DEL_TREE, YDB_DEL_NODE};

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct YDBError (Vec<u8>, i32);

impl fmt::Display for YDBError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "YDB Error ({}): {}", self.1, String::from_utf8_lossy(&self.0))
    }
}

impl error::Error for YDBError {
    fn cause(&self) -> Option<&error::Error> {
        Some(self)
    }
}

pub type YDBResult<T> = Result<T, YDBError>;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
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

/// Provides a Key object for the given subscripts.
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate yottadb;
/// use yottadb::simple_api::Key;
/// let mut my_key: Key = make_key!("^MyTimeSeriesData", "5");
/// ```
#[macro_export]
macro_rules! make_key {
    ( $($x: expr),* ) => (
        {
            let mut key = Key::with_capacity(10);
            $(
                key.push(Vec::from($x));
            )*
            key
        }
    )
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Key {
    buffer_structs: Vec<ydb_buffer_t>,
    buffers: Vec<Vec<u8>>,
    needs_sync: bool,
}

impl Key {
    pub fn with_capacity(num_subscripts: usize) -> Key {
        let empty_struct = ydb_buffer_t{buf_addr: ptr::null_mut(), len_used: 0, len_alloc: 0};
        // We allocate one additional buffer to handle return values
        let mut buffer_structs = Vec::with_capacity(num_subscripts);
        buffer_structs.resize(num_subscripts, empty_struct);
        let buffers = Vec::with_capacity(num_subscripts);
        Key{buffer_structs, buffers, needs_sync: true}
    }

    /// Gets the value of this key from the database
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_GVUNDEF, YDB_ERR_INVSVN, YDB_ERR_LVUNDEF as appropriate if no such variable or node exists;
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::craw::YDB_NOTTP;
    /// use yottadb::simple_api::Key;
    /// let mut key = make_key!("^hello");
    /// let mut output_buffer = Vec::with_capacity(1024);
    ///
    /// output_buffer = key.get_st(YDB_NOTTP, output_buffer).unwrap();
    ///
    /// assert_eq!(String::from_utf8_lossy(&output_buffer), "Hello world!");
    /// ```
    pub fn get_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        let status = unsafe {
            ydb_get_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut out_buffer_t)
        };
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.get_st(tptoken, out_buffer);
        }
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        unsafe {
            out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
        }
        if status != YDB_OK as i32 {
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn set_st(&mut self, tptoken: u64, out_buffer: Vec<u8>, new_val: &Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let mut new_val_t = ydb_buffer_t {
            buf_addr: new_val.as_ptr() as *const _ as *mut _,
            len_alloc: new_val.capacity() as u32,
            len_used: new_val.len() as u32,
        };

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        // Do the call
        let status = unsafe {
            ydb_set_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut new_val_t)
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
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn data_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<(DataReturn, Vec<u8>)> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        let mut retval: u32 = 0;
        // Do the call
        let status = unsafe {
            ydb_data_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut retval as *mut _)
        };
        // Set length of the vec containing the buffer to we can see the value
        if status != YDB_OK as i32 {
            // We could end up with a buffer of a larger size if we couldn't fit the error string
            // into the out_buffer, so make sure to pick the smaller size
            unsafe {
                out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
            }
            return Err(YDBError(out_buffer, status));
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

    pub fn delete_st(&mut self, tptoken: u64, out_buffer: Vec<u8>, delete_type: DeleteType)
            -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        // Do the call
        let status = unsafe {
            ydb_delete_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, match delete_type {
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
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn incr_st(&mut self, tptoken: u64, out_buffer: Vec<u8>, increment: Option<&Vec<u8>>)
            -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);
        let increment_t = match increment {
            None => ptr::null_mut(),
            Some(new_val) => {
                &mut ydb_buffer_t {
                    buf_addr: new_val.as_ptr() as *const _ as *mut _,
                    len_alloc: new_val.capacity() as u32,
                    len_used: new_val.len() as u32,
                } as *mut _
            }
        };

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        // Do the call
        let status = unsafe {
            ydb_incr_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, increment_t, &mut out_buffer_t)
        };
        // Handle resizing the buffer, if needed
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.incr_st(tptoken, out_buffer, increment);
        }
        // Set length of the vec containing the buffer to we can see the value
        if status != YDB_OK as i32 {
            // We could end up with a buffer of a larger size if we couldn't fit the error string
            // into the out_buffer, so make sure to pick the smaller size
            unsafe {
                out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
            }
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn node_next_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        let mut ret_subs_used = (self.buffers.len() - 1) as i32;
        // Do the call
        let status = unsafe {
            ydb_node_next_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut ret_subs_used as *mut _, subscripts)
        };
        // Handle resizing the buffer, if needed
        if status == YDB_ERR_INVSTRLEN {
            let ret_subs_used = (ret_subs_used + 1) as usize;
            self.buffers[ret_subs_used].resize_with(self.buffer_structs[ret_subs_used].len_used as usize, Default::default);
            self.needs_sync = true;
            return self.node_next_self_st(tptoken, out_buffer);
        }
        if status == YDB_ERR_INSUFFSUBS {
            let ret_subs_used = (ret_subs_used + 1) as usize;
            self.buffers.resize_with(ret_subs_used, Default::default);
            self.needs_sync = true;
            return self.node_next_self_st(tptoken, out_buffer);
        }
        // Set length of the vec containing the buffer to we can see the value
        if status != YDB_OK as i32 {
            // We could end up with a buffer of a larger size if we couldn't fit the error string
            // into the out_buffer, so make sure to pick the smaller size
            unsafe {
                out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
            }
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn node_prev_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        let mut ret_subs_used = (self.buffers.len() - 1) as i32;
        // Do the call
        let status = unsafe {
            ydb_node_previous_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut ret_subs_used as *mut _, subscripts)
        };
        // Handle resizing the buffer, if needed
        if status == YDB_ERR_INVSTRLEN {
            let ret_subs_used = (ret_subs_used + 1) as usize;
            self.buffers[ret_subs_used].resize_with(self.buffer_structs[ret_subs_used].len_used as usize, Default::default);
            self.needs_sync = true;
            return self.node_prev_self_st(tptoken, out_buffer);
        }
        if status == YDB_ERR_INSUFFSUBS {
            let ret_subs_used = (ret_subs_used + 1) as usize;
            self.buffers.resize_with(ret_subs_used, Default::default);
            self.needs_sync = true;
            return self.node_prev_self_st(tptoken, out_buffer);
        }
        // Set length of the vec containing the buffer to we can see the value
        if status != YDB_OK as i32 {
            // We could end up with a buffer of a larger size if we couldn't fit the error string
            // into the out_buffer, so make sure to pick the smaller size
            unsafe {
                out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
            }
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn sub_next_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        let status = unsafe {
            ydb_subscript_next_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut out_buffer_t)
        };
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.sub_next_st(tptoken, out_buffer);
        }
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        unsafe {
            out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
        }
        if status != YDB_OK as i32 {
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn sub_prev_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
        // Safe to unwrap because there will never be a buffer_structs with size less than 1
        let mut out_buffer_t = Self::make_out_buffer_t(&mut out_buffer);

        // Get pointers to the varname and to the first subscript
        let (varname, subscripts) = self.get_varname_and_subscripts();
        let status = unsafe {
            ydb_subscript_previous_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut out_buffer_t)
        };
        if status == YDB_ERR_INVSTRLEN {
            out_buffer.resize_with(out_buffer_t.len_used as usize, Default::default);
            return self.sub_prev_st(tptoken, out_buffer);
        }
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        unsafe {
            out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
        }
        if status != YDB_OK as i32 {
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn sub_next_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
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
        let (varname, subscripts) = self.get_varname_and_subscripts();
        let status = unsafe {
            ydb_subscript_next_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut last_self_buffer)
        };
        if status == YDB_ERR_INVSTRLEN {
            self.buffers.last_mut().unwrap().resize_with(out_buffer_t.len_used as usize, Default::default);
            self.needs_sync = true;
            return self.sub_next_self_st(tptoken, out_buffer);
        }
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        unsafe {
            self.buffers.last_mut().unwrap().set_len(min(last_self_buffer.len_alloc, last_self_buffer.len_used) as usize);
        }
        if status != YDB_OK as i32 {
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    pub fn sub_prev_self_st(&mut self, tptoken: u64, out_buffer: Vec<u8>) -> YDBResult<Vec<u8>> {
        let mut out_buffer = out_buffer;
        if self.needs_sync {
            self.sync();
        }
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
        let (varname, subscripts) = self.get_varname_and_subscripts();
        let status = unsafe {
            ydb_subscript_previous_st(tptoken, &mut out_buffer_t, varname, (self.buffers.len() - 1) as i32,
                subscripts, &mut last_self_buffer)
        };
        if status == YDB_ERR_INVSTRLEN {
            self.buffers.last_mut().unwrap().resize_with(out_buffer_t.len_used as usize, Default::default);
            self.needs_sync = true;
            return self.sub_prev_self_st(tptoken, out_buffer);
        }
        // Resize the vec with the buffer to we can see the value
        // We could end up with a buffer of a larger size if we couldn't fit the error string
        // into the out_buffer, so make sure to pick the smaller size
        unsafe {
            self.buffers.last_mut().unwrap().set_len(min(last_self_buffer.len_alloc, last_self_buffer.len_used) as usize);
        }
        if status != YDB_OK as i32 {
            return Err(YDBError(out_buffer, status));
        }
        Ok(out_buffer)
    }

    fn make_out_buffer_t(out_buffer: &mut Vec<u8>) -> ydb_buffer_t {
        ydb_buffer_t {
            buf_addr: out_buffer.as_mut_ptr() as *mut _,
            len_alloc: out_buffer.capacity() as u32,
            len_used: 0,
        }
    }

    fn get_varname_and_subscripts(&mut self) -> (*mut ydb_buffer_t, *mut ydb_buffer_t) {
        let num_subscripts = self.buffer_structs.len();
        match num_subscripts {
            1 => (&mut self.buffer_structs[0] as *mut _, ptr::null_mut()),
            _ => {
                let (a, b) = self.buffer_structs.split_at_mut(1);
                (&mut a[0] as *mut _, &mut b[0] as *mut _)
            },
        }
    }

    fn sync(&mut self) {
        self.buffer_structs.resize_with(self.buffers.len(), Default::default);
        for (i, buff) in self.buffers.iter_mut().enumerate() {
            self.buffer_structs[i].buf_addr = buff.as_mut_ptr() as *mut _;
            self.buffer_structs[i].len_alloc = buff.capacity() as u32;
            self.buffer_structs[i].len_used = buff.len() as u32;
        }
        self.needs_sync = false;
    }
}

impl Deref for Key {
    type Target = Vec<Vec<u8>>;

    fn deref(&self) -> &Self::Target {
        &self.buffers
    }
}

impl DerefMut for Key {
    fn deref_mut(&mut self) -> &mut Vec<Vec<u8>> {
        self.needs_sync = true;
        &mut self.buffers
    }
}

/// Passes the callback function as a structure to the callback
struct CallBackStruct<'a> {
    cb: &'a Fn(u64, Vec<u8>) -> YDBResult<Vec<u8>>,
}

extern "C" fn fn_callback(tptoken: u64, errstr: *mut ydb_buffer_t,
                          tpfnparm: *mut c_void) -> i32 {
    let callback_struct: &mut CallBackStruct =
        unsafe { &mut *(tpfnparm as *mut CallBackStruct) };
    let vec = unsafe {
        Vec::from_raw_parts((*errstr).buf_addr as *mut u8, (*errstr).len_alloc as usize, (*errstr).len_used as usize) 
    };
    let (vec, retval) = match (callback_struct.cb)(tptoken, vec) {
        Ok(vec) => (vec, YDB_OK as i32),
        Err(YDBError(vec, ret)) => (vec, ret),
    };
    mem::forget(vec);
    retval
}

pub fn tp_st(tptoken: u64, out_buffer: Vec<u8>,
             f: &Fn(u64, Vec<u8>) -> YDBResult<Vec<u8>>,
             trans_id: &str,
             locals_to_reset: &[Vec<u8>]) -> YDBResult<Vec<u8>> {
    let mut out_buffer = out_buffer;
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
    let mut callback_struct = CallBackStruct { cb: &f };
    let arg = &mut callback_struct as *mut _ as *mut c_void;
    let status = unsafe {
        ydb_tp_st(tptoken, &mut out_buffer_t, Some(fn_callback), arg, c_str.as_ptr(),
            locals.len() as i32, locals_ptr)
    };
    if status != YDB_OK as i32 {
        unsafe {
            out_buffer.set_len(min(out_buffer_t.len_used, out_buffer_t.len_alloc) as usize);
        }
        return Err(YDBError(out_buffer, status));
    }
    Ok(out_buffer)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_make_key() {
        Key::with_capacity(32);
    }

    #[test]
    fn can_access_key() {
        // Alloc an array of 2 ydb_buffer_t
        let mut key = Key::with_capacity(2);
        // Set the global and subscripts; each of these ends up not doing any
        // additional copying
        key.push(Vec::from("^hello"));
        let sub = Vec::from("world");
        key.push(sub);
    }

    #[test]
    fn basic_set_and_get_st() {
        let mut result = Vec::with_capacity(1);
        let mut key = Key::with_capacity(1);
        key.push(Vec::from("^hello"));

        // Try setting a value
        result = key.set_st(0, result, &Vec::from("Hello world!")).unwrap();
        // Then try getting the value we set
        result = match key.get_st(0, result) {
            Ok(x) => x,
            Err(YDBError(x, _)) => {
                panic!("YDB Error: {}", String::from_utf8_lossy(&x));
            }
        };
        assert_eq!(result, Vec::from("Hello world!"));
    }

    #[test]
    fn ydb_get_st_error() {
        let result = Vec::with_capacity(1);
        let mut key = Key::with_capacity(1);
        key.push(Vec::from("^helloDoesntExist"));
        match key.get_st(0, result) {
            Ok(x) => {
                assert!(false, "Expected error return from key.get_st");
                x
            },
            Err(_) => {
                Vec::from("")
            }
        };
    }

    #[test]
    fn ydb_data_st() {
        let result = Vec::with_capacity(1);
        let mut key = Key::with_capacity(1);
        key.push(Vec::from("^helloDoesNotExist"));

        let (retval, _) = key.data_st(0, result).unwrap();
        assert_eq!(retval, DataReturn::NoData);
    }

    #[test]
    fn ydb_delete_st() {
        let mut result = Vec::with_capacity(1);
        let mut key = Key::with_capacity(1);
        key.push(Vec::from("^helloDeleteMe"));

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
        let mut key = Key::with_capacity(1);
        key.push(Vec::from("^helloIncrementMe"));

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
        match key.node_next_self_st(0, result) {
            Ok(x) => x,
            Err(YDBError(v, x)) => panic!("Failed ({}): {}", x, String::from_utf8_lossy(&v)),
        };
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
        match key.node_next_self_st(0, result) {
            Ok(x) => x,
            Err(YDBError(v, x)) => panic!("Failed ({}): {}", x, String::from_utf8_lossy(&v)),
        };
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
        match key.node_prev_self_st(0, result) {
            Ok(x) => x,
            Err(YDBError(v, x)) => panic!("Failed ({}): {}", x, String::from_utf8_lossy(&v)),
        };
    }

    #[test]
    fn ydb_node_prev_self_extra_node_st() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloNodeprev2", "worlds", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[2] = Vec::from("hyrule");
        result = key.set_st(0, result, &value).unwrap();
        // TODO: why does this break things?
        //key.truncate(2);
        key[1] = Vec::from("z");
        match key.node_prev_self_st(0, result) {
            Ok(x) => x,
            Err(YDBError(v, x)) => panic!("Failed ({}): {}", x, String::from_utf8_lossy(&v)),
        };
    }

    #[test]
    fn ydb_subscript_next() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubNext", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::with_capacity(1);
        result = key.sub_next_st(0, result).unwrap();
        assert_eq!(result, Vec::from("shire"));
    }

    #[test]
    fn ydb_subscript_prev() {
        let mut result = Vec::with_capacity(1);
        let value = Vec::from("Hello world!");
        let mut key = make_key!("^helloSubprev", "shire");
        result = key.set_st(0, result, &value).unwrap();
        key[1] = Vec::from("z");
        result = key.sub_prev_st(0, result).unwrap();
        assert_eq!(result, Vec::from("shire"));
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
        let result = Vec::with_capacity(1);
        tp_st(0, result, &|_tptoken: u64, out: Vec<u8>| -> YDBResult<Vec<u8>> {
            Ok(out)
        }, "BATCH", &Vec::new()).unwrap();
    }
}
