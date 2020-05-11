/****************************************************************
*                                                               *
* Copyright (c) 2020 YottaDB LLC and/or its subsidiaries.       *
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
/// [`ci_tab_open_t`]: fn.ci_tab_open_t.html
/// [`ci_tab_switch_t`]: fn.ci_tab_switch_t.html
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct CallInTableDescriptor(usize);

/// Open the call-in table stored in `file` and return its file descriptor.
///
/// You can later switch the active call-in table by calling [`ci_tab_switch_t`] with the file descriptor.
///
/// # See also
/// - [C SimpleAPI documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-ci-tab-open-ydb-ci-tab-open-t)
/// - [Call-in interface](https://docs.yottadb.com/ProgrammersGuide/extrout.html#call-in-interface)
/// - [`ci_t!`] and [`cip_t!`]
/// - [`ci_tab_switch_t`](fn.ci_tab_switch_t.html)
///
/// # Errors

// The upstream documentation says
// > YDB_ERR_PARAMINVALID if the input parameters fname or ret_value are NULL; or
// PARAMINVALID is not possible because `ptr` and `&mut ret_val` are always non-null.

/// - a negative [error return code] (for example, if the call-in table in the file had parse errors).
///
/// [`ci_tab_switch_t`]: fn.ci_tab_switch_t.html
/// [`ci_t!`]: ../../macro.ci_t.html
/// [`cip_t!`]: ../../macro.cip_t.html
/// [error return code]: https://docs.yottadb.com/MessageRecovery/errormsgref.html#zmessage-codes
///
/// # Example
/// ```
/// # fn main() -> yottadb::YDBResult<()> {
/// use std::ffi::CString;
/// use yottadb::{simple_api::call_in, TpToken};
///
/// let file = CString::new("examples/m-ffi/calltab.ci").unwrap();
/// let descriptor = call_in::ci_tab_open_t(TpToken::default(), Vec::new(), &file)?;
/// # Ok(())
/// # }
pub fn ci_tab_open_t(
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
/// `new_handle` is a file descriptor returned by [`ci_tab_open_t`].
///
/// # Errors

// The upstream docs say this:
// > YDB_ERR_PARAMINVALID if the output parameter ret_old_handle is NULL or if the input parameter new_handle points to an invalid handle (i.e. not returned by a prior ydb_ci_tab_open()/ydb_ci_tab_open_t()) call)
// YDB_ERR_PARAMINVALID isn't possible because
// a) we always pass in `&ret_val`, which is non-null, and
// b) we pass in a handle from `CallInDescriptor`, which can only be created by `ci_tab_open_t`

/// - [a negative error return code](https://docs.yottadb.com/MessageRecovery/errormsgref.html#standard-error-codes)
///
/// [`ci_tab_open_t`]: fn.ci_tab_open_t.html
///
/// # Example
/// ```
/// # fn main() -> yottadb::YDBResult<()> {
/// use std::ffi::CString;
/// use yottadb::{simple_api::call_in, TpToken};
/// let file = CString::new("examples/m-ffi/calltab.ci").unwrap();
/// let (descriptor, err_buf) = call_in::ci_tab_open_t(TpToken::default(), Vec::new(), &file)?;
/// let old_ci_table = call_in::ci_tab_switch_t(TpToken::default(), err_buf, descriptor)?;
/// # Ok(())
/// # }
/// ```
pub fn ci_tab_switch_t(
    tptoken: TpToken, err_buffer: Vec<u8>, new_handle: CallInTableDescriptor,
) -> YDBResult<(CallInTableDescriptor, Vec<u8>)> {
    use crate::craw::ydb_ci_tab_switch_t;

    let mut ret_val: usize = 0;
    let buf = resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| unsafe {
        ydb_ci_tab_switch_t(tptoken, err_buffer_p, new_handle.0, &mut ret_val)
    })?;
    Ok((CallInTableDescriptor(ret_val), buf))
}

/// Make an FFI call to M.
///
/// `ci_t` is equivalent to a variadic function with the following signature:
/// ```ignore
/// unsafe fn ci_t(tptoken: u64, err_buffer: Vec<u8>, routine: &CStr, ...) -> YDBResult<Vec<u8>>;
/// ```
/// However, since Rust does not allow implementing variadic functions, it is a macro instead.
///
/// # Safety
/// Each argument passed (after `routine`) must correspond to the appropriate argument expected by `routine`.
/// If `routine` returns a value, the first argument must be a pointer to an out parameter in which to store the value.
/// All arguments must be [representable as C types][repr-c].
///
/// # See also
/// - [C to M FFI](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#calling-m-routines)
/// - [The M documentation on call-ins](https://docs.yottadb.com/ProgrammersGuide/extrout.html#calls-from-external-routines-call-ins)
/// - [`cip_t!`](../macro.cip_t.html), which allows caching the `routine` lookup, making future calls faster.
///
/// # Example
/// Call the M routine described by `HelloWorld1` in the call-in table.
/// See also `examples/m-ffi/helloworld1.m` and `examples/m-ffi/calltab.ci`.
/// ```
/// use std::env;
/// use std::ffi::CString;
/// use std::os::raw::c_char;
/// use yottadb::{craw, ci_t, TpToken};
///
/// env::set_var("ydb_routines", "examples/m-ffi");
/// env::set_var("ydb_ci", "examples/m-ffi/calltab.ci");
///
/// let mut buf = Vec::<u8>::with_capacity(100);
/// let mut msg = craw::ydb_string_t { length: 100, address: buf.as_mut_ptr() as *mut c_char };
/// let routine = CString::new("HelloWorld1").unwrap();
/// unsafe {
///     ci_t!(TpToken::default(), Vec::with_capacity(100), &routine, &mut msg as *mut _).unwrap();
///     buf.set_len(msg.length as usize);
/// }
/// assert_eq!(&buf, b"entry called");
/// ```
/// [repr-c]: https://doc.rust-lang.org/nomicon/ffi.html#interoperability-with-foreign-code
#[macro_export]
macro_rules! ci_t {
    ($tptoken: expr, $err_buffer: expr, $routine: expr $(, $args: expr)* $(,)?) => {{
        let tptoken: $crate::TpToken = $tptoken;
        let err_buffer: ::std::vec::Vec<u8> = $err_buffer;
        let routine: &::std::ffi::CStr = $routine;

        $crate::simple_api::resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| {
            $crate::craw::ydb_ci_t(tptoken, err_buffer_p, routine.as_ptr(), $($args),*)
        })
    }}
}

/// A call-in descriptor for use with [`cip_t!`].
///
/// This represents an M function described in a call-in table.
/// The descriptor is lazily initialized on the first call to `cip_t!`,
/// and future calls will be much faster to execute.
///
/// [`cip_t!`]: ../../macro.cip_t.html
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

/// Make a FFI call to M using a cached function descriptor.
///
/// `cip_t` is equivalent to a variadic function with the following signature:
/// ```ignore
/// unsafe fn ci_t(tptoken: u64, err_buffer: Vec<u8>, routine: CallInDescriptor, ...) -> YDBResult<Vec<u8>>;
/// ```
/// However, since Rust does not allow implementing variadic functions, it is a macro instead.
///
/// # See also
/// - [`CallInDescriptor`](simple_api/struct.CallInDescriptor.html)
/// - [`ci_t!`](macro.ci_t.html), which has more information about call-ins in YottaDB.
///
/// # Safety
/// Each argument passed (after `routine`) must correspond to the appropriate argument expected by `routine`.
/// If `routine` returns a value, the first argument must be a pointer to an out parameter in which to store the value.
/// All arguments must be [representable as C types][repr-c].
///
/// [repr-c]: https://doc.rust-lang.org/nomicon/ffi.html#interoperability-with-foreign-code
///
/// # Example
/// Call the M routine described by `HelloWorld1` in the call-in table.
/// See also `examples/m-ffi/helloworld1.m` and `examples/m-ffi/calltab.ci`.
/// ```
/// use std::env;
/// use std::ffi::CString;
/// use std::os::raw::c_char;
/// use yottadb::{craw, cip_t, CallInDescriptor, TpToken};
///
/// env::set_var("ydb_routines", "examples/m-ffi");
/// env::set_var("ydb_ci", "examples/m-ffi/calltab.ci");
///
/// let mut buf = Vec::<u8>::with_capacity(100);
/// let mut msg = craw::ydb_string_t { length: 100, address: buf.as_mut_ptr() as *mut c_char };
/// let mut routine = CallInDescriptor::new(CString::new("HelloWorld1").unwrap());
/// unsafe {
///     cip_t!(TpToken::default(), Vec::with_capacity(100), &mut routine, &mut msg as *mut _).unwrap();
///     buf.set_len(msg.length as usize);
/// }
/// assert_eq!(&buf, b"entry called");
/// ```
#[macro_export]
macro_rules! cip_t {
    ($tptoken: expr, $err_buffer: expr, $routine: expr, $($args: expr),* $(,)?) => {{
        let tptoken: $crate::TpToken = $tptoken;
        let err_buffer: ::std::vec::Vec<u8> = $err_buffer;
        let routine: &mut $crate::simple_api::call_in::CallInDescriptor = $routine;

        $crate::simple_api::resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| {
            $crate::craw::ydb_cip_t(tptoken, err_buffer_p, routine.as_mut_ptr(), $($args),*)
        })
    }}
}

#[cfg(test)]
mod test {
    use serial_test::serial;
    use std::env;
    use std::ffi::CString;
    use std::os::raw::c_char;
    use super::*;
    use crate::craw::{self, ydb_string_t, ydb_long_t};
    use crate::YDB_NOTTP;

    fn call<F: FnOnce() -> T, T>(f: F) -> T {
        env::set_var("ydb_routines", "examples/m-ffi");
        env::set_var("ydb_ci", "examples/m-ffi/calltab.ci");
        f()
    }

    // no arguments already tested by doc-test
    #[test]
    fn string_args() {
        call(|| {
            let mut routine = CallInDescriptor::new(CString::new("HelloWorld2").unwrap());

            let mut ret_buf = Vec::<u8>::with_capacity(100);
            let mut ret_msg =
                ydb_string_t { length: 100, address: ret_buf.as_mut_ptr() as *mut c_char };

            let buf1 = b"parm1";
            let mut msg1 = ydb_string_t { length: 5, address: buf1.as_ptr() as *mut c_char };

            let buf2 = b"parm2";
            let mut msg2 = ydb_string_t { length: 5, address: buf2.as_ptr() as *mut c_char };

            let buf3 = b"parm3";
            let mut msg3 = ydb_string_t { length: 5, address: buf3.as_ptr() as *mut c_char };

            unsafe {
                cip_t!(
                    YDB_NOTTP,
                    Vec::with_capacity(100),
                    &mut routine,
                    &mut ret_msg,
                    &mut msg1 as *mut _,
                    &mut msg2 as *mut _,
                    &mut msg3 as *mut _
                )
                .unwrap();
                ret_buf.set_len(ret_msg.length as usize);
            };
            assert_eq!(&ret_buf, b"parm3parm2parm1");
        });
    }
    #[test]
    fn int_args() {
        call(|| {
            use crate::craw::ydb_long_t;

            let mut routine = CallInDescriptor::new(CString::new("Add").unwrap());
            let a = 1 as ydb_long_t;
            let b = 2 as ydb_long_t;
            let mut out = 0;
            unsafe {
                cip_t!(YDB_NOTTP, Vec::with_capacity(100), &mut routine, &mut out, a, b).unwrap();
            }
            assert_eq!(out, 3);
            // make sure it works if called multiple times
            unsafe {
                cip_t!(YDB_NOTTP, Vec::with_capacity(100), &mut routine, &mut out, a, b).unwrap();
            }
            assert_eq!(out, 3);
            // make sure it works with `ci_t`
            let mut routine = routine.into_cstr();
            unsafe {
                ci_t!(YDB_NOTTP, Vec::with_capacity(100), &mut routine, &mut out, a, b).unwrap();
            }
            assert_eq!(out, 3);
        });
    }
    #[test]
    fn no_args() {
        call(|| {
            let mut routine = CStr::from_bytes_with_nul(b"noop\0").unwrap();
            unsafe {
                ci_t!(YDB_NOTTP, Vec::new(), &mut routine).unwrap();
            }
        });
    }
    #[test]
    fn no_callin_env_var() {
        // NOTE: this does NOT set ydb_ci
        env::set_var("ydb_routines", "examples/m-ffi");

        let file = CString::new("examples/m-ffi/calltab.ci").unwrap();
        let (descriptor, err_buf) = ci_tab_open_t(YDB_NOTTP, Vec::new(), &file).unwrap();
        ci_tab_switch_t(YDB_NOTTP, err_buf, descriptor).unwrap();

        // same as doc-test for `ci_t`
        let mut buf = Vec::<u8>::with_capacity(100);
        let mut msg = ydb_string_t { length: 100, address: buf.as_mut_ptr() as *mut c_char };
        let routine = CString::new("HelloWorld1").unwrap();
        unsafe {
            ci_t!(YDB_NOTTP, Vec::with_capacity(100), &routine, &mut msg as *mut _).unwrap();
            buf.set_len(msg.length as usize);
        }
        assert_eq!(&buf, b"entry called");
    }
    #[test]
    #[serial]
    fn tab_open_switch() {
        // NOTE: this does NOT set ydb_ci
        env::set_var("ydb_routines", "examples/m-ffi");

        let small_file = CString::new("examples/m-ffi/small_calltab.ci").unwrap();
        let mut routine = CallInDescriptor::new(CString::new("Add").unwrap());
        let a = 1 as ydb_long_t;
        let b = 2 as ydb_long_t;
        let mut out = 0;

        // first try a table that doesn't have `Add`
        let (small_fd, _) = ci_tab_open_t(YDB_NOTTP, Vec::new(), &small_file).unwrap();
        ci_tab_switch_t(YDB_NOTTP, Vec::new(), small_fd).unwrap();

        let err = unsafe {
            cip_t!(YDB_NOTTP, Vec::with_capacity(100), &mut routine, &mut out, a, b).unwrap_err()
        };
        assert_eq!(err.status, -craw::YDB_ERR_CINOENTRY);
        assert_eq!(out, 0);

        // now try a table that does
        let big_file = CString::new("examples/m-ffi/calltab.ci").unwrap();
        let (big_fd, _) = ci_tab_open_t(YDB_NOTTP, Vec::new(), &big_file).unwrap();
        let (small_fd, _) = ci_tab_switch_t(YDB_NOTTP, Vec::new(), big_fd).unwrap();

        unsafe {
            cip_t!(YDB_NOTTP, Vec::with_capacity(100), &mut routine, &mut out, a, b).unwrap()
        };
        assert_eq!(out, 3);

        // make sure the call works even though the calltable has been changed back
        out = 0;
        ci_tab_switch_t(YDB_NOTTP, Vec::new(), small_fd).unwrap();
        unsafe {
            cip_t!(YDB_NOTTP, Vec::with_capacity(100), &mut routine, &mut out, a, b).unwrap()
        };
        assert_eq!(out, 3);

        // make sure the old descriptor still works and updates the `Add` function name when called with `ci_t`
        let mut routine = routine.into_cstr();
        out = 0;
        let err = unsafe {
            ci_t!(YDB_NOTTP, Vec::with_capacity(100), &mut routine, &mut out, a, b).unwrap_err()
        };
        assert_eq!(err.status, -craw::YDB_ERR_CINOENTRY);
        assert_eq!(out, 0);

        // switch back the calltable to use an environment variable now that we're done
        ci_tab_switch_t(YDB_NOTTP, Vec::new(), CallInTableDescriptor::default()).unwrap();
    }
    #[test]
    #[serial]
    // Test that M FFI works from within a transaction
    fn call_in_tp() {
        use crate::simple_api::{tp_st, TransactionStatus};

        // Set up environment variables
        call(|| {
            let do_callin = |tptoken| {
                // Create a C string with a no-op M function
                let mut routine = CStr::from_bytes_with_nul(b"noop\0").unwrap();
                unsafe {
                    // Call the `noop` M function
                    ci_t!(tptoken, Vec::new(), &mut routine).unwrap();
                }
                Ok(TransactionStatus::Ok)
            };
            // Start a transaction before making the call
            tp_st(YDB_NOTTP, Vec::new(), do_callin, "BATCH", &[]).unwrap();
        });
    }
}
