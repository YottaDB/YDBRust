extern crate bindgen;
extern crate pkg_config;

use std::env;
use std::path::PathBuf;

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

    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg(include_path)
        .whitelist_type("ydb_.*")
        .whitelist_function("ydb_.*")
        .whitelist_var("YDB_.*")
        // for `ydb_lock`
        .whitelist_type("gparam_list.*")
        .whitelist_var("MAXVPARMS")
        .blacklist_item("YDB_NOTTP")
        // Finish the builder and generate the bindings.
        .generate()
        // Unwrap the Result and panic on failure.
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
