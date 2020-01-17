#![allow(non_snake_case)]

use yottadb::simple_api::{DeleteType, Key};
use yottadb::craw::YDB_NOTTP;

fn main() {
	let err_buffer = Vec::with_capacity(1024);
	let mut hello = Key::new("hello", &["Rust"]);
	let err_buffer = hello.set_st(YDB_NOTTP, err_buffer, "こんにちは".as_bytes()).unwrap();

	let out_buffer = Vec::with_capacity(100);
	let out_buffer = hello.get_st(YDB_NOTTP, out_buffer).unwrap();
	assert_eq!(out_buffer, "こんにちは".as_bytes());
	hello.delete_st(YDB_NOTTP, err_buffer, DeleteType::DelNode).unwrap();
}
