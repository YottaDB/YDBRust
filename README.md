
# YDBRust - Rust Bindings for YottaDB

YottaDB is a multi-language NoSQL database. 

All software in this package is part of YottaDB (https://yottadb.com), each
file of which identifies its copyright holders. The software is made available
to you under the terms of a license. Refer to the LICENSE file for details.

Homepage: https://gitlab.com/YottaDB/Lang/YDBRust

## Using YDBRust in your project

Include YDBRust in your Cargo.toml:

```
[dependencies]
yottadb = { git = "https://gitlab.com/YottaDB/Lang/YDBRust.git" }

```

Add this into your project:

```
extern crate yottadb;

use yottadb::simple_api::Key;

```

Before building or using a project which depends on YottaDB, you need to ensure that YottaDB is set up and configured.

```
source $(pkg-config --variable=prefix yottadb)/ydb_env_set

```

## Development Setup

Fork the YDBRust repository on Gitlab, clone it to your machine, and then use it for development.

```
git clone https://gitlab.com/YottaDB/Lang/YDBRust.git

cd YDBRust

source $(pkg-config --variable=prefix yottadb)/ydb_env_set

cargo test

cargo doc --open

```
