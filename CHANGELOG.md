<!--
Copyright (c) 2020 YottaDB LLC and/or its subsidiaries.
All rights reserved.

      This source code contains the intellectual property
      of its copyright holder(s), and is made available
      under a license.  If you do not know the terms of
      the license, please stop and do not read further.
-->

# Changelog

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
