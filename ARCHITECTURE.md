# Overview

There are two main APIs, the `simple_api` and `context_api`, plus the auto-generated C bindings.

The auto-generated C bindings are called `craw` and are created directly from the yottadb header files using [bindgen].
The functions are difficult to use from safe Rust, but several of the constants,
like `YDB_NOTTP` and the `YDB_ERR_*`, are used elsewhere in the wrapper.

The `simple_api` corresponds closely to the C Simple API,
but handles reallocation and also converts error codes from C into `YDBResult`.
`Result` is the canonical way to do error handling in Rust,
see [the book][book-result] for more info.
This API also aims to be 'safe' (see [below](#safety-in-rust)).

The `context_api` aims to be easy to use while avoiding excessive copies.
Unlike the `easy_api` in Go, there is no unnecessary allocation
(not quite true: there is an [extra error buffer] created when
starting a new transaction).
The API is meant to look like a key/value store instead of FFI.

## Simple API

The `simple_api` is the most complicated part of the wrapper.
As mentioned above, it has three jobs:

- Handle reallocation if there is not enough space in a buffer
- Convert error codes returned by the YDB API to `Result`
- Be ['safe'](#safety-in-rust) (i.e. avoid undefined behavior)

### Implementation

Currently, the `simple_api` works like this:

There is a public-facing `buffers` struct which allows arbitrary changes.
This allows code like this to compile:

```rust
let mut key = Key::variable("^hello");
key.push("world");
key[1] = "Philadelphia";
```

However, there is a problem:
[`Vec`], the dynamically resizable array type in Rust, is not FFI-compatible
with `ydb_buffer_t` (i.e. it may have a different ABI layout).
This means that every `Vec` must be converted to `ydb_buffer_t`
before it can be passed to the C API.
Fortunately, we don't need to copy the entire buffer, we only need to copy
the (capacity, length, ptr) metadata. This is done with `make_out_buffer_t`.

TODO: write up why `make_out_buffer_t` should return a `ydb_buffer_t` with a bounded lifetime (but doesn't).

Instead of copying the metadata for every variable and subscript on each call,
there is a separate internal `self.buffer_structs` data structure.
This is meant to be exactly the same as the `self.buffers` structure,
but FFI compatible. That means that it has to be kept in sync:
`buffer_structs` _must_ be updated to the state of `buffers` before any call
to the C API.

NOTE: this is about to change, see [#12]

There is one more catch: on breadth- and depth-first traversal of the tree,
the `Key` is updated by the YDB API. In this case, we need to do a
`reverse_sync`, which updates _`buffers`_ with _`buffer_structs`_.

## Context API

The `context_api` is the simplest part of the wrapper.
It is a very simple wrapper around the `simple_api` which
keeps track of an internal `buffer` and `tptoken`.
Everything else is offloaded to the `simple_api`.

The `context_api` also has several `Iterator` implementations that are
mostly generated with macros. I have not used these `Iterator`s and don't
know how they work, but they aren't necessary for using the API.

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
[#12]: https://gitlab.com/YottaDB/Lang/YDBRust/issues/12#note_277563001
