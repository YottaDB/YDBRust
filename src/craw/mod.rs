//! A wrapper for C YottaDB API (the C Raw API, CRAW)
//!
//! This contains things like error codes, return values, constants,
//! new functionality not yet wrapped in the simple API, and other fun
//! things, but is dangerous to use. Unless you have a good reason, use the
//! Simple API.
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(unknown_lints)]
#![allow(clippy::all)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// Currently, bindgen doesn't produce calculated values
//  Add them here as needed
pub const YDB_INT_MAX: i32 = 0x7fffffff;
/// The constant used to indicate a [transaction] should be restarted.
///
/// # See also
/// - [`ydb_tp_st`](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-tp-s-ydb-tp-st)
/// - [Simple API docs](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#normal-return-codes)
///
/// [transaction]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing
pub const YDB_TP_RESTART: i32 = (YDB_INT_MAX - 1); /* 0x7ffffffe */
/// The constant that indicates a [transaction] should be rolled back.
/// This can be used in conjunction with [`ydb_tp_st`]
/// to rollback an ongoing transaction.
///
/// [transaction]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing
/// [`ydb_tp_st`]: https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-tp-s-ydb-tp-st
pub const YDB_TP_ROLLBACK: i32 = (YDB_INT_MAX - 2); /* 0x7ffffffd */
/// The constant used by [`ydb_node_next_st()`]
/// to indicate that the end of a node has been reached.
///
/// [`ydb_node_next_st()`]: https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-node-next-s-ydb-node-next-st
pub const YDB_NODE_END: i32 = (YDB_INT_MAX - 3); /* 0x7ffffffc */
/// The constant used to indicate that timeout occurred while acquiring a [lock].
///
/// # See also
/// - [`ydb_lock_incr_st`](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-incr-s-ydb-incr-st)
///
/// [lock]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#locks
pub const YDB_LOCK_TIMEOUT: i32 = (YDB_INT_MAX - 4); /* 0x7ffffffb */
/// An error code returned by [`ydb_file_is_identical_t()`].
///
/// [`ydb_file_is_identical_t()`]: https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-file-is-identical-ydb-file-is-identical-t
pub const YDB_NOTOK: i32 = (YDB_INT_MAX - 5); /* 0x7ffffffa */
/// The constant used to indicate that no [transaction] is ongoing.
///
/// [transaction]: https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#transaction-processing
pub const YDB_NOTTP: u64 = 0;
