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

//! YottaDB is a NoSQL Database suitable for high-performance systems.
//!
//! YottaDB runs in-process, like SQLite, with no need for a daemon.
//! This crate is a Rust wrapper around the C implementation of YottaDB.
//!
//! There are three major APIs:
//! - `craw`, the FFI bindings generated directly by bindgen.
//!     These are not recommended for normal use,
//!     but are available in case the other APIs are missing functionality.
//! - `simple_api`, a wrapper around the `craw` API
//!     which handles resizing buffers and various other recoverable errors.
//!     The simple API also provides a `YDBError` struct so that errors are
//!     returned as `Result` instead of an error code.
//! - `context_api`, which is a wrapper around the `simple_api` that
//!     stores the current tptoken and an error buffer
//!     so you don't have to keep track of them yourself.
//!     The reason the context_api is necessary is because this crate binds to
//!     the threaded version of YottaDB, which requires a `tptoken` and `err_buffer`.
//!     See [transaction processing] for more details on transactions and `tptoken`s.
//!
//! The context_api is recommended for normal use, but the others are available if your
//! needs are more specialized.
//!
//! [transaction processing]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing
#![deny(missing_docs)]

pub mod context_api;
#[allow(missing_docs)]
pub mod craw;
pub mod simple_api;

pub use craw::{YDB_NOTTP, YDB_ERR_GVUNDEF, YDB_ERR_LVUNDEF};
pub use simple_api::{CallInDescriptor, CallInTableDescriptor, DataReturn, DeleteType, TransactionStatus, YDBError, YDBResult};

use std::os::raw::c_int;
/// Cleans up the process connection/access to all databases and all yottadb data structures.
///
/// If you have already made a call to YottaDB, any future calls to YottaDB after calling `yottadb::exit()`
/// will return `YDBError { status: YDB_ERR_CALLINAFTERXIT }`.
/// If you have never before made a call to YottaDB, `exit()` has no effect.
///
/// A typical application should not need to call `yottadb::exit()`
/// since YottaDB will automatically clean up on process termination.
///
/// This has no effect on any `Key`s, which will be automatically dropped when they go out of scope.
///
/// # Errors
/// - `YDB_ERR_INVYDBEXIT` if `exit()` is called through M FFI (e.g. through `simple_api::ci_t`)
///
/// Possible errors for this function include:
/// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
///
/// # Example
// this is no_run because otherwise all other tests will get YDB_ERR_CALLINAFTERXIT
/// ```no_run
/// yottadb::ydb_exit();
/// ```
pub fn ydb_exit() -> c_int {
    unsafe { craw::ydb_exit() }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::ffi::CString;

    // These tests are ignored since if they run, all future calls will fail
    #[test]
    #[ignore]
    fn test_exit_before_init() {
        // If called before any previous ydb_* call, should do nothing.
        ydb_exit();
        simple_api::Key::variable("a").data_st(YDB_NOTTP, Vec::new()).unwrap();
    }

    #[test]
    #[ignore]
    fn test_exit() {
        // Calls should work to start
        simple_api::Key::variable("a").data_st(YDB_NOTTP, Vec::new()).unwrap();
        ydb_exit();
        // Then calls return CALLINAFTERXIT after calling `exit()`
        let err = simple_api::Key::variable("a").data_st(YDB_NOTTP, Vec::new()).unwrap_err();
        assert_eq!(err.status, craw::YDB_ERR_CALLINAFTERXIT);
    }

    #[test]
    #[ignore]
    fn test_invalid_exit() {
        use std::env::set_var;
        use crate::craw::ydb_string_t;

        set_var("ydb_routines", "examples/m-ffi");
        set_var("ydb_ci", "examples/m-ffi/calltab.ci");
        set_var("ydb_xc_c", "examples/m-ffi/external.xc");

        // `INVYDBEXIT` should be returned if `exit` is called through M FFI
        let mut buf = Vec::<u8>::with_capacity(1000);

        let mut status =
            ydb_string_t { address: buf.as_mut_ptr() as *mut _, length: buf.capacity() as u64 };
        let exit = CString::new("ydb_exit").unwrap();
        unsafe {
            ci_t!(YDB_NOTTP, Vec::new(), &exit, &mut status as *mut ydb_string_t).unwrap();
            buf.set_len(status.length as usize);
        }

        let msg = String::from_utf8_lossy(&buf);
        println!("{:?}", msg);
        let status = msg.split(',').next().unwrap().parse().expect("status should be valid number");
        assert_eq!(-craw::YDB_ERR_INVYDBEXIT, status);
    }
}
