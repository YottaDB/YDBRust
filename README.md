[![pipeline status](https://gitlab.com/YottaDB/Lang/YDBRust/badges/master/pipeline.svg)](https://gitlab.com/YottaDB/Lang/YDBRust/commits/master)


# YDBRust - Rust Bindings for YottaDB

YottaDB is a multi-language NoSQL database.

All software in this package is part of YottaDB (https://yottadb.com), each
file of which identifies its copyright holders. The software is made available
to you under the terms of a license. Refer to the LICENSE file for details.

Homepage: https://gitlab.com/YottaDB/Lang/YDBRust

Documentation: https://yottadb.gitlab.io/Lang/YDBRust/yottadb/

## Using YDBRust in your project

Include YDBRust in your Cargo.toml:

```toml
[dependencies]
yottadb = "0.1"
```

Add this into your project:

```rust
extern crate yottadb;

use yottadb::simple_api::Key;
```

Before building or using a project which depends on YottaDB, you need to ensure that YottaDB is set up and configured.

```sh
source $(pkg-config --variable=prefix yottadb)/ydb_env_set
```

## Development Setup

Fork the YDBRust repository on Gitlab, clone it to your machine, and then use it for development.

```sh
git clone https://gitlab.com/YottaDB/Lang/YDBRust.git

cd YDBRust

source $(pkg-config --variable=prefix yottadb)/ydb_env_set

# install dependencies for bindgen
# NOTE: this does not necessarily need apt, this is just an example
sudo apt update && sudo apt install clang

cargo test

cargo doc --open
```

You may want to also set up pre-commit hooks:

`ln -s ../../test.sh .git/hooks/pre-commit`

### Developing with Docker

Alternatively, you can use the provided dockerfile:

```sh
docker build --tag ydbrust .
docker run --volume "${PWD}":/opt/ydbrust -it ydbrust bash
source $(pkg-config --variable=prefix yottadb)/ydb_env_set
cargo test
cargo doc
```

The documentation will be available locally at
`file:///path/to/ydbrust/target/doc/yottadb/index.html`.
