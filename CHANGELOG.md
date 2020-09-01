<!--
Copyright (c) 2020 YottaDB LLC and/or its subsidiaries.
All rights reserved.

      This source code contains the intellectual property
      of its copyright holder(s), and is made available
      under a license.  If you do not know the terms of
      the license, please stop and do not read further.
-->

# Changelog

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
