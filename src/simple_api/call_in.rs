/****************************************************************
*                                                               *
* Copyright (c) 2021 YottaDB LLC and/or its subsidiaries.       *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

//! A 'Call In' is an FFI call from Rust to M.
//!
//! Call-ins usually go through `ci_t`, but `cip_t` is also available for better performance.
//!
//! # See also
//! - [Using External Calls](https://docs.yottadb.com/ProgrammersGuide/extrout.html#using-external-calls)

use std::ffi::{CString, CStr};
use crate::craw::ci_name_descriptor;
use super::{resize_call, YDBResult, TpToken};

/// The descriptor for a call-in table opened with [`ci_tab_open_t`].
///
/// `CallInTableDescriptor::default()` returns a table which,
/// when called with [`ci_tab_switch_t`], uses the environment variable `ydb_ci`.
/// This is also the table that is used if `ci_tab_switch_t` is never called.
///
/// [`ci_tab_open_t`]: ci_tab_open_t()
/// [`ci_tab_switch_t`]: ci_tab_switch_t()
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct CallInTableDescriptor(usize);

/// Open the call-in table stored in `file` and return its file descriptor.
///
/// See also [Context::ci_tab_open](crate::context_api::Context::ci_tab_open).
pub(crate) fn ci_tab_open_t(
    tptoken: TpToken, err_buffer: Vec<u8>, file: &CStr,
) -> YDBResult<(CallInTableDescriptor, Vec<u8>)> {
    use crate::craw::ydb_ci_tab_open_t;

    // this cast is safe because YDB never modifies the string
    let ptr = file.as_ptr() as *mut _;
    let mut ret_val: usize = 0;
    let buf = resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| unsafe {
        ydb_ci_tab_open_t(tptoken, err_buffer_p, ptr, &mut ret_val)
    })?;
    Ok((CallInTableDescriptor(ret_val), buf))
}

/// Switch the active call-in table to `new_handle`. Returns the previously active table.
///
/// See also [Context::ci_tab_switch](crate::context_api::Context::ci_tab_switch).
pub(crate) fn ci_tab_switch_t(
    tptoken: TpToken, err_buffer: Vec<u8>, new_handle: CallInTableDescriptor,
) -> YDBResult<(CallInTableDescriptor, Vec<u8>)> {
    use crate::craw::ydb_ci_tab_switch_t;

    let mut ret_val: usize = 0;
    let buf = resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| unsafe {
        ydb_ci_tab_switch_t(tptoken, err_buffer_p, new_handle.0, &mut ret_val)
    })?;
    Ok((CallInTableDescriptor(ret_val), buf))
}

/// A call-in descriptor for use with [`cip_t!`].
///
/// This represents an M function described in a call-in table.
/// The descriptor is lazily initialized on the first call to `cip_t!`,
/// and future calls will be much faster to execute.
///
/// [`cip_t!`]: crate::cip_t!
pub struct CallInDescriptor(ci_name_descriptor);

impl CallInDescriptor {
    /// Create a new `descriptor` that will call `routine`.
    pub fn new(routine: CString) -> Self {
        use crate::craw::ydb_string_t;
        use std::os::raw::c_ulong;

        let string = ydb_string_t {
            length: routine.as_bytes().len() as c_ulong,
            address: routine.into_raw(),
        };
        Self(ci_name_descriptor { rtn_name: string, handle: std::ptr::null_mut() })
    }
    /// Consume this descriptor and return the original routine
    pub fn into_cstr(self) -> CString {
        let cstr = unsafe { CString::from_raw(self.0.rtn_name.address) };
        std::mem::forget(self);
        cstr
    }
    // this needs to be public so it can be used in a macro
    #[doc(hidden)]
    pub fn as_mut_ptr(&mut self) -> *mut ci_name_descriptor {
        &mut self.0
    }
}

impl Drop for CallInDescriptor {
    fn drop(&mut self) {
        // TODO: this is doing the same thing as `into_cstr`
        drop(unsafe { CString::from_raw(self.0.rtn_name.address) })
    }
}
