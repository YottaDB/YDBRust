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
use std::hash::{Hash, Hasher};
use std::ptr;

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// Currently, bindgen doesn't produce calculated values
//  Add them here as needed
pub const YDB_INT_MAX: i32 = 0x7fffffff;
pub const YDB_TP_RESTART: i32 = (YDB_INT_MAX - 1); /* 0x7ffffffe */
pub const YDB_TP_ROLLBACK: i32 = (YDB_INT_MAX - 2); /* 0x7ffffffd */
pub const YDB_NODE_END: i32 = (YDB_INT_MAX - 3); /* 0x7ffffffc */
pub const YDB_LOCK_TIMEOUT: i32 = (YDB_INT_MAX - 4); /* 0x7ffffffb */
pub const YDB_NOTOK: i32 = (YDB_INT_MAX - 5); /* 0x7ffffffa */
pub const YDB_NOTTP: u64 = 0;


// Derive some attributes for things
impl Hash for ydb_buffer_t {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len_alloc.hash(state);
        self.len_used.hash(state);
        self.buf_addr.hash(state);
    }
}

impl PartialEq for ydb_buffer_t {
    fn eq(&self, other: &ydb_buffer_t) -> bool {
        self.buf_addr == other.buf_addr && self.len_used == other.len_used
            && self.len_alloc == other.len_alloc
    }
}

impl Eq for ydb_buffer_t { }

impl Default for ydb_buffer_t {
    fn default() -> Self {
        ydb_buffer_t {
            buf_addr: ptr::null_mut(),
            len_alloc: 0,
            len_used: 0,
        }
    }
}
