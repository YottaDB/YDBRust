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
pub mod craw;
pub mod simple_api;
pub mod context_api;

pub use craw::{YDB_NOTTP, YDB_ERR_GVUNDEF, YDB_ERR_LVUNDEF};
pub use simple_api::{DataReturn, DeleteType, YDBError, YDBResult};
