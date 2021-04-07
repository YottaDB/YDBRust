<!--
Copyright (c) 2020-2021 YottaDB LLC and/or its subsidiaries.
All rights reserved.

      This source code contains the intellectual property
      of its copyright holder(s), and is made available
      under a license.  If you do not know the terms of
      the license, please stop and do not read further.
-->

# Changelog

## Unreleased

### Added

- Added [`Key::last_mut`], which is a shorter and non-panicking version of `&mut key[key.len() - 1]`.

### Changed

- The `simple_api` is now private. We recommend using the `context_api` instead.
  TODO: write up a migration guide.
- The `tptoken` field of `YDBError` is now private. This prevents infinite hangs, aborts, or other bugs
  when calling `error.to_string()` on an error with an invalid tptoken. As a side effect,
  `YDBError` cannot be constructed outside of the `yottadb` crate.
- The `context_api` module is now hidden from the documentation and its items are re-exported at
  the crate root; we recommend using the top-level items instead. However, it still remains public to make migration to 2.0 easier.
- `KeyContext::next_sub` and `prev_sub` now return a `Vec<u8>` buffer instead of a full `KeyContext`. To replicate the old behavior, you can use this snippet:

```rust
let mut new_key = key.clone();
new_key.next_sub_self()?;
```

## [1.2.0] - 2021-02-07

### Fixed

- The following functions can no longer cause memory corruption when resizing buffers
  ([!118](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/118)):
  + [`Key::sub_next_self_st`](https://yottadb.gitlab.io/Lang/YDBRust/yottadb/simple_api/struct.Key.html#method.sub_next_self_st)
  + [`Key::sub_prev_self_st`](https://yottadb.gitlab.io/Lang/YDBRust/yottadb/simple_api/struct.Key.html#method.sub_prev_self_st)
  + [`KeyContext::next_sub_self`](https://yottadb.gitlab.io/Lang/YDBRust/yottadb/context_api/struct.KeyContext.html#method.next_sub_self)
  + [`KeyContext::prev_sub_self`](https://yottadb.gitlab.io/Lang/YDBRust/yottadb/context_api/struct.KeyContext.html#method.prev_sub_self)

  See [the test case](https://gitlab.com/YottaDB/Lang/YDBRust/-/blob/086ea414229022b93579cac8bb967415c449a764/src/simple_api/tests.rs#L939)
  for details about exactly how this could break before.

- `impl Error for YDBError` no longer returns itself in `fn cause()`. This avoids infinite loops when iterating over the source of an error.
  [!115](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/115)
- Returning a `YDBError` from inside a transaction no longer discards the error buffer.
  Previously, the error buffer would always be shown as empty even if an error occurred.
  [!121](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/121)
- The test suite is now thread-safe. Note that this is only changed the test suite, the main YDBRust API has always been thread-safe.
  [!112](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/112)

### Added

- `yottadb` no longer requires compiling `bindgen` from source (when passed `--no-default-features`).
  See [!101](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/101/pipelines) for details.
- `KeyContext` now implements `AddAssign` as a shortcut for `increment()`. [!113](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/113)
- `u64` now implements `From<Tptoken>`. Previously, `u64::from(tptoken)` would be a compile error even though `let u: u64 = tptoken.into()` worked correctly. [!122](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/122)
- Various `Debug` implementations are more readable. [!111](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/111)

### Changed

- The minimum supported Rust version (MSRV) has been increased to 1.40. [!110]
- Errors for transactions are now required to implement `Send` and `Sync`. [!99](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/99)
- Various dependencies have been updated. [!110]

[!110]: https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/110

## [1.1.0] - 2020-09-01

### Fixed

- `ci_t!` and `ci_t_p!` can no longer loop forever if passed an output buffer with insufficient capacity ([!98](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/98))
- Several broken links in the documentation have been fixed ([!95](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/95))

## [1.0.0] - 2020-08-17

### Added

- Types shared between the `context_api` and `simple_api`, such as `YDBError`, are now re-exported at the top level ([!40](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/40))
- The following C Simple API functions are now exposed:
  + `ydb_delete_excl_st` ([!46](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/46))
  + `ydb_lock_{incr,decr}_st` ([!48](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/48))
  + `ydb_str2zwr` and `ydb_zwr2_str` ([!51](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/51))
  + `ydb_lock_st` ([!55](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/55))
  + `ydb_eintr_handler_t` ([!86](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/86))
  + Utility functions ([!68](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/68))
    - `ydb_message`
    - `ydb_ci_tab_open_t`
    - `ydb_ci_tab_switch_t`
    - `ydb_ci_t`
    - `ydb_cip_t`
    - `ydb_exit`

- Added `release_st` ([!68](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/68)) printing the version of the Rust wrapper
- Added compatibility with Rust 1.34 ([!75](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/75))
- `tp_st` now allows rolling back or restarting a transaction ([!65](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/65))
- `ParseError` now implements `std::error::Error` ([!71](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/71))
- Added many more tests and documention:
  + [!53](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/53)
  + [!58](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/58)
  + [!62](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/62)
  + [!63](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/63)
  + [!86](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/86)
  + [!88](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/88)

### Changed

- `TpToken` is now its own type instead of a `u64`, to prevent passing in an invalid tptoken ([!76](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/76)).
- `tp_st` now takes a slice of strings instead of a slice of `Vec` ([!64](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/64))
- `bindgen` is now built in debug mode even when YDBRust is built in release mode, greatly improving compile times ([!81](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/81))
- The buffers in the `context_api` are no longer pre-allocated, greatly reducing memory usage ([!82](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/82))
- `bindgen` has been updated to `0.54` ([!91](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/91))

### Fixed

- Many crashes, panics, and segfaults have been fixed. See variously
  + [!42](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/42)
  + [!43](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/43)
  + [!49](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/49)
  + [!52](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/52)

- `incr_st` no longer increments twice when passed an `out_buffer` that is too small ([!44](https://gitlab.com/YottaDB/Lang/YDBRust/-/merge_requests/44))

## [0.3.0] - 2020-02-03

### Removed

- Removed `impl DerefMut<Target = Vec<u8>> for Key` in favor of more specific methods and impls

### Changed

- The `add_st()`, `set_st()`, and `delete_st()` functions now take `&Key` instead of `&mut Key`,
  making the borrow semantics easier to work with. See [#12](https://gitlab.com/YottaDB/Lang/YDBRust/issues/12) for more details.
- Updated bindgen to 0.52, removing several unnecessary dependencies

## [0.2.0] - 2020-01-27

### Fixed

- Fix [double-free when calling `key.truncate`](https://gitlab.com/YottaDB/Lang/YDBRust/issues/14)

### Added

- `KeyContext::get_and_parse()` convenience function

### Changed

- Use `truncate()` or `resize()` instead of `set_len()` in documentation and examples
