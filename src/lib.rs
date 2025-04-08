/**********************************************************************
*                                                                     *
* Copyright (c) 2019-2021, 2025 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                                *
*                                                                     *
*       This source code contains the intellectual property           *
*       of its copyright holder(s), and is made available             *
*       under a license.  If you do not know the terms of             *
*       the license, please stop and do not read further.             *
*                                                                     *
***********************************************************************/
#![deny(missing_docs)]
#![allow(clippy::upper_case_acronyms)]
// too many false positives: https://github.com/rust-lang/rust-clippy/issues/14275#issuecomment-2786492705
#![allow(clippy::doc_overindented_list_items)]

//! [YottaDB] is a NoSQL Database suitable for high-performance systems.
//!
//! YottaDB runs in-process, like SQLite, with no need for a daemon.
//! This crate is a Rust wrapper around the C implementation of YottaDB.
//!
//! There are two major APIs:
//! - [`craw`], the FFI bindings generated directly by bindgen.
//!     These are not recommended for normal use,
//!     but are available in case the Context API is missing functionality.
//! - The main Context API, which is a safe wrapper around the C API which
//!     stores the current tptoken and an error buffer so you don't have to keep track of them yourself.
//!     The reason this metadata is necessary is because this crate binds to the threaded version of
//!     YottaDB, which requires a `tptoken` and `err_buffer`. See [transaction processing] for more
//!     details on transactions and `tptoken`s.
//!
//! Most operations are encapsulated in methods in the [`KeyContext`] struct.
//! Iteration helpers are available to iterate over values in the database in a variety of ways.
//!
//! # Examples
//!
//! A basic database operation (set a value, retrieve it, and delete it)
//!
//! ```
//! use yottadb::{Context, KeyContext, DeleteType, YDBResult};
//!
//! fn main() -> YDBResult<()> {
//!     let ctx = Context::new();
//!     let mut key = KeyContext::new(&ctx, "^MyGlobal", &["SubscriptA", "42"]);
//!     key.set("This is a persistent message")?;
//!     let buffer = key.get()?;
//!     assert_eq!(&buffer, b"This is a persistent message");
//!     key.delete(DeleteType::DelNode)?;
//!     Ok(())
//! }
//! ```
//!
//! # Intrinsic Variables
//!
//! YottaDB has several intrinsic variables which are documented [online][intrinsics].
//! To get the value of these variables, call `get_st` on a `Key` with the name of the variable.
//!
//! ## Example
//!
//! Get the instrinsic variable [`$tlevel`][tlevel], which gives the current transaction level.
//!
//! ```
//! use yottadb::{Context, KeyContext, YDB_NOTTP, YDBResult};
//!
//! fn main() -> YDBResult<()> {
//!     let ctx = Context::new();
//!     let mut key = KeyContext::variable(&ctx, "$tlevel");
//!     let tlevel: usize = String::from_utf8_lossy(&key.get()?).parse()
//!         .expect("$tlevel should be an integer");
//!     assert_eq!(tlevel, 0_usize);
//!     Ok(())
//! }
//! ```
//!
//! # Features
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
//! # Signal handling
//!
//! YottaDB performs its own signal handling in addition to any signal handlers you may have set up.
//! Since many functions in C are not async-safe, it defers any action until the next time `ydb_eintr_handler` is called.
//! All YDB functions will automatically call `ydb_eintr_handler` if necessary,
//! so in most cases this should not affect your application. However, there are some rare cases
//! when the handler will not be called:
//! - If you have a tight loop inside a [`Context::tp`] that does not call a YDB function
//!
//! For example, the following loop will run forever even if sent SIGINT:
//! ```no_run
//! # fn main() -> yottadb::YDBResult<()> {
//! use yottadb::{Context, KeyContext};
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
//! To avoid this, call [`Context::eintr_handler`] in the loop:
//!
//! ```no_run
//! # fn main() -> yottadb::YDBResult<()> {
//! # use yottadb::{Context, KeyContext};
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
//! ## See also
//!
//! - The [C documentation on signals](https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#signals)
//! - [`Context::eintr_handler`]
//! - [`Context::tp`](crate::Context::tp)
//!
//! [YottaDB]: https://yottadb.com/
//! [transaction processing]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing
//! [intrinsics]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#intrinsic-special-variables
//! [tlevel]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#tlevel

/// This is the entry-point of the `yottadb` crate. See
/// <https://doc.rust-lang.org/book/ch07-02-defining-modules-to-control-scope-and-privacy.html>
/// for more information; it calls this module the "crate root".
///
/// The root contains functions and data shared between both the simple and context API.
#[allow(unused)]
const INTERNAL_DOCS: () = ();

/// Public to reduce churn when upgrading versions, but it's recommended to use the top-level re-exports instead.
#[doc(hidden)]
pub mod context_api;
#[allow(missing_docs)]
pub mod craw;
mod simple_api;

pub use craw::{YDB_ERR_GVUNDEF, YDB_ERR_LVUNDEF};
#[doc(inline)] // needed because of rust-lang/rust#81890
pub use context_api::*; // glob import so we catch all the iterators
pub use simple_api::{
    call_in::{CallInDescriptor, CallInTableDescriptor},
    DataReturn, DeleteType, Key, TransactionStatus, TpToken, YDBError, YDBResult,
};
#[doc(hidden)]
/// This has to be public so that it can be used by `ci_t!`.
/// However, it is not a supported part of the API.
pub use simple_api::resize_call;

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
/// - `YDB_ERR_INVYDBEXIT` if `ydb_exit()` is called through M FFI (e.g. through [`ci_t`])
///
/// Possible errors for this function include:
/// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
///
/// # Example
// this is no_run because otherwise all other tests will get YDB_ERR_CALLINAFTERXIT
/// ```no_run
/// yottadb::ydb_exit();
/// ```
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
