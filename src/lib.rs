/****************************************************************
*                                                               *
* Copyright (c) 2019-2021 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

//! [YottaDB] is a NoSQL Database suitable for high-performance systems.
//!
//! YottaDB runs in-process, like SQLite, with no need for a daemon.
//! This crate is a Rust wrapper around the C implementation of YottaDB.
//!
//! There are three major APIs:
//! - [`craw`], the FFI bindings generated directly by bindgen.
//!     These are not recommended for normal use,
//!     but are available in case the other APIs are missing functionality.
//! - [`simple_api`], a wrapper around the `craw` API
//!     which handles resizing buffers and various other recoverable errors.
//!     The simple API also provides a [`YDBError`] struct so that errors are
//!     returned as `Result` instead of an error code.
//! - [`context_api`], which is a wrapper around the `simple_api` that
//!     stores the current tptoken and an error buffer
//!     so you don't have to keep track of them yourself.
//!     The reason the context_api is necessary is because this crate binds to
//!     the threaded version of YottaDB, which requires a `tptoken` and `err_buffer`.
//!     See [transaction processing] for more details on transactions and `tptoken`s.
//!
//! The context_api is recommended for normal use, but the others are available if your
//! needs are more specialized.
//!
//! ## Features
//!
//! Since `yottadb` is a set of bindings to a C library, it uses `bindgen` to generate the bindings.
//! There are two ways to do this:
//! - `features = ["vendor"]`, the default. This compiles `bindgen` from source.
//! - `default-features = false`. This requires you to have bindgen already installed locally.
//!
//! Using vendoring means you can use `yottadb` in any user environment,
//! even when you don't have admin priviledges to install programs.
//! Using a pre-installed version means compile times are much lower.
//!
//! ## Signal handling
//!
//! YottaDB performs its own signal handling in addition to any signal handlers you may have set up.
//! Since many functions in C are not async-safe, it defers any action until the next time `ydb_eintr_handler` is called.
//! All YDB functions will automatically call `ydb_eintr_handler` if necessary,
//! so in most cases this should not affect your application. However, there are some rare cases
//! when the handler will not be called:
//! - If you have a tight loop inside a [`tp`] that does not call a YDB function
//!
//! For example, the following loop will run forever even if sent SIGINT:
//! ```no_run
//! # fn main() -> yottadb::YDBResult<()> {
//! use yottadb::context_api::{Context, KeyContext};
//! let ctx = Context::new();
//! let loop_callback = |_| loop {
//!     std::thread::sleep(std::time::Duration::from_secs(1));
//!     println!("finished sleep");
//! };
//! ctx.tp(loop_callback, "BATCH", &[]).unwrap();
//! # Ok(())
//! # }
//! ```
//!
//! To avoid this, call [`eintr_handler`] in the loop:
//!
//! ```no_run
//! # fn main() -> yottadb::YDBResult<()> {
//! # use yottadb::context_api::{Context, KeyContext};
//! # let ctx = Context::new();
//! # let release = ctx.release()?;
//! loop {
//!     std::thread::sleep(std::time::Duration::from_secs(1));
//!     ctx.eintr_handler()?;
//!     println!("finished sleep");
//! }
//! # }
//! ```
//!
//! However, you should endeavor to keep transactions as short as possible -
//! both for performance, since YottaDB uses optimistic concurrency control,
//! and for reliability, since operations will not be committed until the transaction concludes.
//!
//! As a last-ditch method of error-recovery, YottaDB will exit immediately
//! if sent three interrupt signals in a row, even if `eintr_handler` is not called.
//!
//! YottaDB does not register any signal handlers until the first time `ydb_init` is called,
//! and deregisters its handlers after `ydb_exit`.
//!
//! ### See also
//!
//! - The [C documentation on signals](https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#signals)
//! - [`eintr_handler`]
//! - [`eintr_handler_t`]
//! - [`tp`]
//!
//! [`YDBError`]: simple_api::YDBError
//! [`eintr_handler`]: context_api::Context::eintr_handler()
//! [`eintr_handler_t`]: simple_api::eintr_handler_t()
//! [`tp`]: context_api::Context::tp()
//! [YottaDB]: https://yottadb.com/
//! [transaction processing]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing
#![deny(missing_docs)]
#![allow(clippy::upper_case_acronyms)]

/// This is the entry-point of the `yottadb` crate. See
/// <https://doc.rust-lang.org/book/ch07-02-defining-modules-to-control-scope-and-privacy.html>
/// for more information; it calls this module the "crate root".
///
/// The root contains functions and data shared between both the simple and context API.
#[allow(unused)]
const INTERNAL_DOCS: () = ();

pub mod context_api;
#[allow(missing_docs)]
pub mod craw;
pub mod simple_api;

pub use craw::{YDB_ERR_GVUNDEF, YDB_ERR_LVUNDEF};
pub use simple_api::{
    call_in::{CallInDescriptor, CallInTableDescriptor},
    DataReturn, DeleteType, TransactionStatus, TpToken, YDBError, YDBResult,
};
// This is not just a convenience for users; there is no way to construct a `TpToken` outside of
// YDBRust because the fields are private.
/// The default transaction processing token if no transaction is in progress.
pub const YDB_NOTTP: TpToken = TpToken(
    // This can't use `TpToken::default` because constants cannot use trait functions.
    craw::YDB_NOTTP,
);

/// Cleans up the process connection/access to all databases and all yottadb data structures.
///
/// If you have already made a call to YottaDB, any future calls to YottaDB after calling `yottadb::ydb_exit()`
/// will return `YDBError { status: YDB_ERR_CALLINAFTERXIT }`.
/// If you have never before made a call to YottaDB, `exit()` has no effect.
///
/// A typical application should not need to call `yottadb::ydb_exit()`
/// since YottaDB will automatically clean up on process termination.
///
/// This has no effect on any [`Key`]s, which will be automatically dropped when they go out of scope.
///
/// # Errors
/// - `YDB_ERR_INVYDBEXIT` if `ydb_exit()` is called through M FFI (e.g. through `simple_api::ci_t`)
///
/// Possible errors for this function include:
/// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
///
/// # Example
// this is no_run because otherwise all other tests will get YDB_ERR_CALLINAFTERXIT
/// ```no_run
/// yottadb::ydb_exit();
/// ```
/// [`Key`]: simple_api::Key
pub fn ydb_exit() -> std::os::raw::c_int {
    unsafe { craw::ydb_exit() }
}

/// The locks in this module prevents data races in the test suite.
///
/// In particular, `delete_excl` and some of the call-in tests interfere with all other concurrent tests.
#[cfg(test)]
mod test_lock {
    use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};
    use once_cell::sync::Lazy;

    #[derive(Debug)]
    #[must_use = "if unused the RwLock will immediately unlock"]
    pub(crate) enum LockGuard<'a> {
        Read(RwLockReadGuard<'a, ()>),
        Write(RwLockWriteGuard<'a, ()>),
    }

    impl LockGuard<'_> {
        /// Use a `Read` lock if the test can be run concurrently with others.
        ///
        /// You may have to use unique variable names for this property to hold.
        pub(crate) fn read() -> Self {
            // If one tests panics, don't cause all others to panic as well.
            let guard = match TEST_LOCK.read() {
                Ok(g) => g,
                Err(poison) => poison.into_inner(),
            };
            LockGuard::Read(guard)
        }

        /// Use a `Write` lock if the test interferes with all other concurrent tests.
        pub(crate) fn write() -> Self {
            // If one tests panics, don't cause all others to panic as well.
            let guard = match TEST_LOCK.write() {
                Ok(g) => g,
                Err(poison) => poison.into_inner(),
            };
            LockGuard::Write(guard)
        }
    }

    /// This lock holds no data, it is used only for synchronization.
    pub(crate) static TEST_LOCK: Lazy<RwLock<()>> = Lazy::new(|| RwLock::new(()));
}
