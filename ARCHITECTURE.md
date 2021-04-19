<!--
Copyright (c) 2020-2021 YottaDB LLC and/or its subsidiaries.
All rights reserved.

      This source code contains the intellectual property
      of its copyright holder(s), and is made available
      under a license.  If you do not know the terms of
      the license, please stop and do not read further.
-->

# Overview

There are two main APIs, the [`simple_api`] and [`context_api`], plus the auto-generated C bindings.

The auto-generated C bindings are called `craw` and are created directly from the yottadb header files using [bindgen].
The functions are difficult to use from safe Rust, but several of the constants,
like `YDB_NOTTP` and the `YDB_ERR_*`, are used elsewhere in the wrapper.

The `simple_api` corresponds closely to the C Simple API,
but handles reallocation and also converts error codes from C into `YDBResult`.
`Result` is the canonical way to do error handling in Rust,
see [the book][book-result] for more info.
This API also aims to be safe (see [below](#safety-in-rust)).
This API is private because it's low-level and not very convenient to use,
to avoid the user having to decide which API they want.

The `context_api` has all the goals of the simple_api, and in addition, aims to be easy to use
while avoiding excessive copies. Unlike the `easy_api` in Go, it does not [allocate on each
call][easy-api-allocate]. The context API only allocates once per Context (or it can also
reallocate if the current buffer doesn't have enough space). Note that nothing about this is
specific to Rust, Go plans to add a context API at some point: [YDBGo#11].

The API is meant to look like a key/value store instead of FFI. This is the only public safe API.

Note there are two public APIs which aren't safe: `ci_t!` and `cip_t!`. These can't reasonable be
made safe because they don't know what types the M function accepts (#46).

[`simple_api`]: https://gitlab.com/YottaDB/Lang/YDBRust/-/tree/master/src/simple_api
[`context_api`]: https://gitlab.com/YottaDB/Lang/YDBRust/-/tree/master/src/context_api
[easy-api-allocate]: https://gitlab.com/YottaDB/Lang/YDBGo/-/blob/793b7a4a41b517f7ec6124d3e765fe2838833586/easy_api.go#L46.
[YDBGo#11]: https://gitlab.com/YottaDB/Lang/YDBGo/-/issues/11

## Simple API

The `simple_api` is the most complicated part of the wrapper.
As mentioned above, it has three jobs:

- Handle reallocation if there is not enough space in a buffer
- Convert error codes returned by the YDB API to `Result`
- Be [safe](#safety-in-rust) (i.e. prevent undefined behavior at compile time)

### Implementation

Currently, the `simple_api` works like this:

1. `Key` allow arbitrary *immutable* access to the buffer of subscripts. This allows viewing the
  length and searching for subscripts, among other things.
2. `Key` allows for select *mutable* access to the buffer of subscripts.
  That allows code like this to compile:

```rust
let mut key = Key::variable("^hello");
key.push(b"world".to_vec());
key[0] = b"Philadelphia".to_vec();
assert_eq!(key, Key::new("^hello", &["Philadelphia"]));
```

Arbitrary mutable access was removed because it makes the API hard to read: not all methods on
`Vec` are relevant, so `Key` only exposes the ones that are useful.

However, there is a problem:
[`Vec`], the dynamically resizable array type in Rust, is not FFI-compatible
with `ydb_buffer_t` (i.e. it may have a different ABI layout).
Rust makes [no guarantees about the layout][repr-rust] unless you explicitly opt-in with [`#[repr(C)]`][repr-c].
which Vec [does not][vec-src]. Vec calls this out explicitly [in the docs][guarantees]:

> Most fundamentally, Vec is and always will be a (pointer, capacity, length) triplet. No more, no less. The order of these fields is completely unspecified, and you should use the appropriate methods to modify these. The pointer will never be null, so this type is null-pointer-optimized.

["null-pointer optimized"](https://stackoverflow.com/a/46557737/7669110) is not super relevant
here, but the basic idea is that by making the layout unstable the compiler can optimize it to
take up less space if you have a non-null pointer somewhere.

This means that every `Vec` must be converted to `ydb_buffer_t`
before it can be passed to the C API.
Fortunately, we don't need to copy the entire buffer, we only need to copy
the (capacity, length, ptr) metadata. This is done with `make_out_buffer_t`.

To avoid having to have different data structures that are kept in sync,
we copy the metadata for every variable and subscript on each call.
This ensures that the metadata is up-to-date for a small performance penalty
(a copy of at most `3*n` machine words), where n is the number of subscripts.
This also has the major advantage of allowing `get()`, `set()`, `data()`,
and `delete()` to be immutable. See [#12] for more discussion.

There is one more catch: if the *number* of subscripts changes, we may need to
reallocate the `subscripts` buffer when it's updated by the YDB API. In this
case, we do a `growing_shrinking_call`, which updates `subscripts` with
the new buffers.

[repr-rust]: https://doc.rust-lang.org/reference/type-layout.html#the-default-representation
[repr-c]: https://doc.rust-lang.org/reference/type-layout.html#the-c-representation
[vec-src]: https://doc.rust-lang.org/1.51.0/src/alloc/vec/mod.rs.html#374-379
[guarantees]: https://doc.rust-lang.org/std/vec/struct.Vec.html#guarantees
## Context API

The `context_api` is the simplest part of YDBRust.
It is a very simple wrapper around the `simple_api` which
keeps track of an internal `buffer` and `tptoken`.
Everything else is offloaded to the `simple_api`.

The `context_api` also has several `Iterator` implementations that are
mostly generated with macros.

## Safety in Rust

Safe is defined in Rust as preventing undefined behavior,
not just for current uses of the API, but for all uses that might exist.
In other words, if a use of the library would cause a segfault,
memory corruption, or other undefined behavior, that use should not compile.
See [the Rustinomicon][undefined behavior] for more details on
what constitutes undefined behavior.
See [dtolnay's excellent writeup][dtolnay-soundness] for more background
on what 'all uses that might exist' means, as well as `unsafe` in general.

[bindgen]: https://rust-lang.github.io/rust-bindgen/
[book-result]: https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html
[undefined behavior]: https://doc.rust-lang.org/nomicon/what-unsafe-does.html
[dtolnay-soundness]: https://docs.rs/dtolnay/0.0.7/dtolnay/macro._03__soundness_bugs.html#soundness
[extra error buffer]: https://gitlab.com/YottaDB/Lang/YDBRust/blob/ca8512d796e31c0bf43b789de10cdc322e0b3a7d/src/context_api/mod.rs#L149
[`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[#12]: https://gitlab.com/YottaDB/Lang/YDBRust/issues/12
