# Changelog

## [0.2.0] - 2020-01-27

### Fixed

- Fix [double-free when calling `key.truncate`](https://gitlab.com/YottaDB/Lang/YDBRust/issues/14)

### Added

- `KeyContext::get_and_parse()` convenience function

### Changes

- Use `truncate()` or `resize()` instead of `set_len()` in documentation and examples
