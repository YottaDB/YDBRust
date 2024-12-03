/****************************************************************
*                                                               *
* Copyright (c) 2020-2024 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

use std::ffi::CStr;

use crate::{YDBResult, simple_api::call_in::*};
use super::Context;

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
/// - [`cip_t!`], which allows caching the `routine` lookup, making future calls faster.
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
/// let mut msg = craw::ydb_string_t { length: buf.capacity() as u64, address: buf.as_mut_ptr() as *mut c_char };
/// let routine = CString::new("HelloWorld1").unwrap();
/// unsafe {
///     ci_t!(TpToken::default(), Vec::new(), &routine, &mut msg as *mut _).unwrap();
///     buf.set_len(msg.length as usize);
/// }
/// assert_eq!(&buf, b"entry called");
/// ```
/// [repr-c]: https://doc.rust-lang.org/nomicon/ffi.html#interoperability-with-foreign-code
/// [`cip_t!`]: crate::cip_t!
#[macro_export]
macro_rules! ci_t {
    ($tptoken: expr, $err_buffer: expr, $routine: expr $(, $args: expr)* $(,)?) => {{
        let tptoken: $crate::TpToken = $tptoken;
        let err_buffer: ::std::vec::Vec<u8> = $err_buffer;
        let routine: &::std::ffi::CStr = $routine;

        $crate::resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| {
            $crate::craw::ydb_ci_t(tptoken, err_buffer_p, routine.as_ptr(), $($args),*)
        })
    }}
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
/// - [`CallInDescriptor`](crate::CallInDescriptor)
/// - [`ci_t!`], which has more information about call-ins in YottaDB.
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
/// let mut msg = craw::ydb_string_t { length: buf.capacity() as u64, address: buf.as_mut_ptr() as *mut c_char };
/// let mut routine = CallInDescriptor::new(CString::new("HelloWorld1").unwrap());
/// unsafe {
///     cip_t!(TpToken::default(), Vec::new(), &mut routine, &mut msg as *mut _).unwrap();
///     buf.set_len(msg.length as usize);
/// }
/// assert_eq!(&buf, b"entry called");
/// ```
/// [`ci_t!`]: crate::ci_t!
#[macro_export]
macro_rules! cip_t {
    ($tptoken: expr, $err_buffer: expr, $routine: expr, $($args: expr),* $(,)?) => {{
        let tptoken: $crate::TpToken = $tptoken;
        let err_buffer: ::std::vec::Vec<u8> = $err_buffer;
        let routine: &mut $crate::CallInDescriptor = $routine;

        $crate::resize_call(tptoken, err_buffer, |tptoken, err_buffer_p| {
            $crate::craw::ydb_cip_t(tptoken, err_buffer_p, routine.as_mut_ptr(), $($args),*)
        })
    }}
}

/// Call-in functions
impl Context {
    /// Open the call-in table stored in `file` and return its file descriptor.
    ///
    /// You can later switch the active call-in table by calling [`ci_tab_switch`] with the file descriptor.
    ///
    /// # See also
    /// - [C SimpleAPI documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-ci-tab-open-ydb-ci-tab-open-t)
    /// - [Call-in interface](https://docs.yottadb.com/ProgrammersGuide/extrout.html#call-in-interface)
    /// - [`ci_t!`] and [`cip_t!`]
    ///
    /// [`cip_t!`]: crate::cip_t!
    /// [`ci_t!`]: crate::ci_t!
    ///
    #[allow(clippy::empty_line_after_doc_comments)]
    /// # Errors

    // The upstream documentation says
    // > YDB_ERR_PARAMINVALID if the input parameters fname or ret_value are NULL; or
    // PARAMINVALID is not possible because `ptr` and `&mut ret_val` are always non-null.

    /// - a negative [error return code] (for example, if the call-in table in the file had parse errors).
    ///
    /// [`ci_tab_switch`]: Context::ci_tab_switch()
    /// [error return code]: https://docs.yottadb.com/MessageRecovery/errormsgref.html#zmessage-codes
    ///
    /// # Example
    /// ```
    /// # fn main() -> yottadb::YDBResult<()> {
    /// use std::ffi::CString;
    /// use yottadb::Context;
    ///
    /// let ctx = Context::new();
    /// let file = CString::new("examples/m-ffi/calltab.ci").unwrap();
    /// let descriptor = ctx.ci_tab_open(&file)?;
    /// # Ok(())
    /// # }
    pub fn ci_tab_open(&self, file: &CStr) -> YDBResult<CallInTableDescriptor> {
        let tptoken = self.tptoken();
        let buffer = self.take_buffer();
        let (descriptor, buffer) = ci_tab_open_t(tptoken, buffer, file)?;
        *self.context.buffer.borrow_mut() = buffer;
        Ok(descriptor)
    }

    /// Switch the active call-in table to `new_handle`. Returns the previously active table.
    ///
    /// `new_handle` is a file descriptor returned by [`ci_tab_open`].
    ///
    #[allow(clippy::empty_line_after_doc_comments)]
    /// # Errors

    // The upstream docs say this:
    // > YDB_ERR_PARAMINVALID if the output parameter ret_old_handle is NULL or if the input parameter new_handle points to an invalid handle (i.e. not returned by a prior ydb_ci_tab_open()/ydb_ci_tab_open_t()) call)
    // YDB_ERR_PARAMINVALID isn't possible because
    // a) we always pass in `&ret_val`, which is non-null, and
    // b) we pass in a handle from `CallInDescriptor`, which can only be created by `ci_tab_open_t`

    /// - [a negative error return code](https://docs.yottadb.com/MessageRecovery/errormsgref.html#standard-error-codes)
    ///
    /// [`ci_tab_open`]: Context::ci_tab_open()
    ///
    /// # Example
    /// ```
    /// # fn main() -> yottadb::YDBResult<()> {
    /// use std::ffi::CString;
    /// use yottadb::Context;
    ///
    /// let ctx = Context::new();
    /// let file = CString::new("examples/m-ffi/calltab.ci").unwrap();
    /// let descriptor = ctx.ci_tab_open(&file)?;
    /// let old_ci_table = ctx.ci_tab_switch(descriptor)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn ci_tab_switch(
        &self, new_handle: CallInTableDescriptor,
    ) -> YDBResult<CallInTableDescriptor> {
        let tptoken = self.tptoken();
        let buffer = self.take_buffer();
        let (descriptor, buffer) = ci_tab_switch_t(tptoken, buffer, new_handle)?;
        *self.context.buffer.borrow_mut() = buffer;
        Ok(descriptor)
    }
}

#[cfg(test)]
mod test {
    use std::env;
    use std::ffi::CString;
    use std::os::raw::c_char;
    use super::*;
    use crate::craw::{self, ydb_string_t, ydb_long_t};
    use crate::YDB_NOTTP;
    use crate::test_lock::LockGuard;

    fn call<F: FnOnce() -> T, T>(f: F) -> T {
        let _guard = LockGuard::read();
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
            let mut ret_msg = ydb_string_t {
                length: ret_buf.capacity() as u64,
                address: ret_buf.as_mut_ptr() as *mut c_char,
            };

            let buf1 = b"parm1";
            let mut msg1 =
                ydb_string_t { length: buf1.len() as u64, address: buf1.as_ptr() as *mut c_char };

            let buf2 = b"parm2";
            let mut msg2 =
                ydb_string_t { length: buf2.len() as u64, address: buf2.as_ptr() as *mut c_char };

            let buf3 = b"parm3";
            let mut msg3 =
                ydb_string_t { length: buf3.len() as u64, address: buf3.as_ptr() as *mut c_char };

            unsafe {
                cip_t!(
                    YDB_NOTTP,
                    Vec::new(),
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
                cip_t!(YDB_NOTTP, Vec::new(), &mut routine, &mut out, a, b).unwrap();
            }
            assert_eq!(out, 3);
            // make sure it works if called multiple times
            unsafe {
                cip_t!(YDB_NOTTP, Vec::new(), &mut routine, &mut out, a, b).unwrap();
            }
            assert_eq!(out, 3);
            // make sure it works with `ci_t`
            let mut routine = routine.into_cstr();
            unsafe {
                ci_t!(YDB_NOTTP, Vec::new(), &mut routine, &mut out, a, b).unwrap();
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
        // This modifies the active call-in table and so cannot run in parallel with other tests in
        // this module.
        let _guard = LockGuard::write();

        // NOTE: this does NOT set ydb_ci
        env::set_var("ydb_routines", "examples/m-ffi");

        let file = CString::new("examples/m-ffi/calltab.ci").unwrap();
        let (descriptor, err_buf) = ci_tab_open_t(YDB_NOTTP, Vec::new(), &file).unwrap();
        ci_tab_switch_t(YDB_NOTTP, err_buf, descriptor).unwrap();

        // same as doc-test for `ci_t`
        let mut buf = Vec::<u8>::with_capacity(100);
        let mut msg = ydb_string_t {
            length: buf.capacity() as u64,
            address: buf.as_mut_ptr() as *mut c_char,
        };
        let routine = CString::new("HelloWorld1").unwrap();
        unsafe {
            ci_t!(YDB_NOTTP, Vec::new(), &routine, &mut msg as *mut _).unwrap();
            buf.set_len(msg.length as usize);
        }
        assert_eq!(&buf, b"entry called");
    }
    #[test]
    fn tab_open_switch() {
        // This test cannot run in parallel with any others.
        let _guard = LockGuard::write();

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

        let err =
            unsafe { cip_t!(YDB_NOTTP, Vec::new(), &mut routine, &mut out, a, b).unwrap_err() };
        assert_eq!(err.status, craw::YDB_ERR_CINOENTRY);
        assert_eq!(out, 0);

        // now try a table that does
        let big_file = CString::new("examples/m-ffi/calltab.ci").unwrap();
        let (big_fd, _) = ci_tab_open_t(YDB_NOTTP, Vec::new(), &big_file).unwrap();
        let (small_fd, _) = ci_tab_switch_t(YDB_NOTTP, Vec::new(), big_fd).unwrap();

        unsafe { cip_t!(YDB_NOTTP, Vec::new(), &mut routine, &mut out, a, b).unwrap() };
        assert_eq!(out, 3);

        // make sure the call works even though the calltable has been changed back
        out = 0;
        ci_tab_switch_t(YDB_NOTTP, Vec::new(), small_fd).unwrap();
        unsafe { cip_t!(YDB_NOTTP, Vec::new(), &mut routine, &mut out, a, b).unwrap() };
        assert_eq!(out, 3);

        // make sure the old descriptor still works and updates the `Add` function name when called with `ci_t`
        let mut routine = routine.into_cstr();
        out = 0;
        let err =
            unsafe { ci_t!(YDB_NOTTP, Vec::new(), &mut routine, &mut out, a, b).unwrap_err() };
        assert_eq!(err.status, craw::YDB_ERR_CINOENTRY);
        assert_eq!(out, 0);

        // switch back the calltable to use an environment variable now that we're done
        ci_tab_switch_t(YDB_NOTTP, Vec::new(), CallInTableDescriptor::default()).unwrap();
    }
    #[test]
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
