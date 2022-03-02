/****************************************************************
*                                                               *
* Copyright (c) 2019-2022 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

use std::env;
use std::path::{PathBuf, Path};

fn main() {
    let yottadb = pkg_config::probe_library("yottadb").unwrap();
    let mut include_path = String::from("-I");
    for path in yottadb.include_paths {
        let s = path.to_str().unwrap();
        include_path.push_str(s);
    }
    let mut library_path = String::from("");
    for path in yottadb.link_paths {
        let s = path.to_str().unwrap();
        library_path.push_str(s);
    }
    println!("cargo:rust-link-search={}", library_path);
    println!("cargo:rerun-if-changed=wrapper.h");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=Cargo.lock");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    let out_path = out_path.join("bindings.rs");

    #[cfg(feature = "vendor")]
    generate_bindings_via_library(include_path, &out_path);

    #[cfg(not(feature = "vendor"))]
    generate_bindings_via_cli(include_path, &out_path);
}

#[cfg(feature = "vendor")]
fn generate_bindings_via_library(include_path: String, out_path: &Path) {
    bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg(include_path)
        .allowlist_type("ydb_.*")
        .allowlist_function("ydb_.*")
        .allowlist_var("YDB_.*")
        // for `ydb_lock`
        .allowlist_type("gparam_list.*")
        .allowlist_var("MAX_GPARAM_LIST_ARGS")
        .blocklist_item("YDB_NOTTP")
        // Finish the builder and generate the bindings.
        .generate()
        // Unwrap the Result and panic on failure.
        .expect("Unable to generate bindings")
        .write_to_file(out_path)
        .expect("Couldn't write bindings!");
}

#[cfg(not(feature = "vendor"))]
fn generate_bindings_via_cli(include_path: String, out_path: &Path) {
    use std::process::Command;

    #[rustfmt::skip] // rustfmt doesn't know the arguments are related
    let args = [
        "wrapper.h",
        "--whitelist-type", "ydb_.*",
        "--whitelist-function", "ydb_.*",
        "--whitelist-var", "YDB_.*",
        "--whitelist-type", "gparam_list.*",
        "--whitelist-var", "MAX_GPARAM_LIST_ARGS",
        "--blacklist-item", "YDB_NOTTP",
        // This was a String originally, so it's safe to unwrap.
        // It only went through `Path` so that the file separator would be right.
        "--output", out_path.to_str().unwrap(),
        "--",
        &include_path,
    ];
    match Command::new("bindgen").args(&args).status() {
        Ok(status) => assert!(status.success(), "error: failed to generate bindings with bindgen\nhelp: there may be more error output above"),
        Err(err) => panic!("error: failed to run bindgen: {}\n\
            help: make sure `bindgen` is installed and in $PATH\n\
            help: consider enabling the `vendor` feature, which compiles `bindgen` from source", err),
    }
}
