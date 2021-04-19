/****************************************************************
*                                                               *
* Copyright (c) 2021 YottaDB LLC and/or its subsidiaries.       *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

use std::num::ParseIntError;
use super::*;

#[test]
fn create() {
    let ctx = Context::new();
    let _ = ctx.new_key("^hello");
    let _ = KeyContext::from((&ctx, "^hello".into()));
    let _ = KeyContext::with_key(&ctx, "^hello");
    let _ = KeyContext::variable(&ctx, "^hi".to_owned());
}

#[test]
fn simple_get() {
    let ctx = Context::new();
    let key = ctx.new_key(Key::variable("^helloGet"));
    key.set(b"Hello world!").unwrap();
    assert_eq!(key.get().unwrap(), b"Hello world!");
    key.delete(DeleteType::DelNode).unwrap();
}

#[test]
fn simple_set() {
    let ctx = Context::new();
    let key = ctx.new_key(Key::variable("helloSet"));
    key.set(b"Hello world!").unwrap();
    key.set("Hello str!").unwrap();
    key.set(String::from("Hello String!")).unwrap();
    key.delete(DeleteType::DelNode).unwrap();
}

#[test]
fn simple_data() {
    let ctx = Context::new();
    let key = ctx.new_key(Key::variable("helloData"));
    key.data().unwrap();
}

#[test]
fn simple_delete() {
    let ctx = Context::new();
    let key = ctx.new_key(Key::variable("^helloDeleteMe"));
    key.set(b"Hello world!").unwrap();
    key.delete(DeleteType::DelNode).unwrap();
}

#[test]
fn simple_increment() {
    let ctx = Context::new();
    let key = ctx.new_key(Key::variable("^helloIncrementMe"));
    key.increment(None).unwrap();
}

#[test]
fn simple_prev_node() {
    let ctx = Context::new();
    let mut key = make_ckey!(ctx, "^helloPrevNode", "0", "0");

    key.set(b"Hello world!").unwrap();
    // Forget the second subscript
    key.truncate(1);
    // Go to the next node, then walk backward
    key[0] = Vec::from("1");
    let k2 = key.prev_node().unwrap();

    assert_eq!(k2[1], b"0");
}

// Macro to test ordered expressions
macro_rules! make_loop_test {
    ($testname:ident, $func:ident, $transform:expr,
        $($pat:pat => $val:expr),*) => {
        #[test]
        fn $testname() {
            let ctx = Context::new();
            let var = String::from(stringify!($testname)).replace("_", "");
            println!("{}", var);
            let mut key = ctx.new_key(Key::new(var, &["shire"]));
            key.delete(DeleteType::DelTree).unwrap();

            key.set(b"Tolkien").unwrap();
            key[0] = Vec::from("mundus");
            key.set(b"Elder Scrolls").unwrap();
            key[0] = dbg!(Vec::from("high garden"));
            key.set(b"Song of Ice and Fire").unwrap();
            assert_eq!(&key[0], b"high garden");
            key[0].clear();
            for (i, x) in key.$func().enumerate() {
                let x = x.unwrap();
                let x = $transform(x.clone());
                assert_eq!(x, match i {
                    $( $pat => $val ),*,
                    _ => panic!("Unexpected value: <{:#?}>", x),
                }, "Values don't match on {}th iteration (for key {:?})", i, key);
            }
        }
    }
}

make_loop_test!(test_iter_values, iter_values, |x: Vec<u8>| {
    String::from_utf8_lossy(&x).into_owned()
},
0 => "Song of Ice and Fire",
1 => "Elder Scrolls",
2 => "Tolkien"
);

make_loop_test!(test_iter_subs, iter_subs, |x: Vec<u8>| {
    String::from_utf8_lossy(&x).into_owned()
},
0 => "high garden",
1 => "mundus",
2 => "shire"
);

make_loop_test!(test_iter_subs_values, iter_subs_values, |(x, y): (Vec<u8>, Vec<u8>)| {
    (String::from_utf8_lossy(&x).into_owned(),
    String::from_utf8_lossy(&y).into_owned())
},
0 => (String::from("high garden"), String::from("Song of Ice and Fire")),
1 => (String::from("mundus"), String::from("Elder Scrolls")),
2 => (String::from("shire"), String::from("Tolkien"))
);

make_loop_test!(test_iter_key_subs, iter_key_subs, |x: KeyContext| {
    (String::from_utf8_lossy(x.key.variable.as_bytes()).into_owned(), String::from_utf8_lossy(&x[0]).into_owned())
},
0 => (String::from("testiterkeysubs"), String::from("high garden")),
1 => (String::from("testiterkeysubs"), String::from("mundus")),
2 => (String::from("testiterkeysubs"), String::from("shire"))
);

make_loop_test!(test_iter_nodes, iter_nodes, |x: Vec<u8>| {
    String::from_utf8_lossy(&x).into_owned()
},
0 => "Song of Ice and Fire",
1 => "Elder Scrolls",
2 => "Tolkien"
);

make_loop_test!(test_iter_key_nodes, iter_key_nodes, |x: KeyContext| {
    (String::from_utf8_lossy(x.key.variable.as_bytes()).into_owned(), String::from_utf8_lossy(&x[0]).into_owned())
},
0 => (String::from("testiterkeynodes"), String::from("high garden")),
1 => (String::from("testiterkeynodes"), String::from("mundus")),
2 => (String::from("testiterkeynodes"), String::from("shire"))
);

make_loop_test!(test_iter_values_reverse, iter_values_reverse, |x: Vec<u8>| {
    String::from_utf8_lossy(&x).into_owned()
},
2 => "Song of Ice and Fire",
1 => "Elder Scrolls",
0 => "Tolkien"
);

make_loop_test!(test_iter_subs_reverse, iter_subs_reverse, |x: Vec<u8>| {
    String::from_utf8_lossy(&x).into_owned()
},
2 => "high garden",
1 => "mundus",
0 => "shire"
);

make_loop_test!(test_iter_subs_values_reverse, iter_subs_values_reverse, |(x, y): (Vec<u8>, Vec<u8>)| {
    (String::from_utf8_lossy(&x).into_owned(),
    String::from_utf8_lossy(&y).into_owned())
},
2 => (String::from("high garden"), String::from("Song of Ice and Fire")),
1 => (String::from("mundus"), String::from("Elder Scrolls")),
0 => (String::from("shire"), String::from("Tolkien"))
);

make_loop_test!(test_iter_key_subs_reverse, iter_key_subs_reverse, |x: KeyContext| {
    (String::from_utf8_lossy(x.key.variable.as_bytes()).into_owned(), String::from_utf8_lossy(&x[0]).into_owned())
},
2 => (String::from("testiterkeysubsreverse"), String::from("high garden")),
1 => (String::from("testiterkeysubsreverse"), String::from("mundus")),
0 => (String::from("testiterkeysubsreverse"), String::from("shire"))
);

make_loop_test!(test_iter_nodes_reverse, iter_nodes_reverse, |x: Vec<u8>| {
    String::from_utf8_lossy(&x).into_owned()
},
2 => "Song of Ice and Fire",
1 => "Elder Scrolls",
0 => "Tolkien"
);

make_loop_test!(test_iter_key_nodes_reverse, iter_key_nodes_reverse, |x: KeyContext| {
    (String::from_utf8_lossy(x.key.variable.as_bytes()).into_owned(), String::from_utf8_lossy(&x[0]).into_owned())
},
2 => (String::from("testiterkeynodesreverse"), String::from("high garden")),
1 => (String::from("testiterkeynodesreverse"), String::from("mundus")),
0 => (String::from("testiterkeynodesreverse"), String::from("shire"))
);

#[test]
fn test_simple_tp() {
    let ctx = Context::new();
    ctx.tp(
        |ctx| {
            let key = ctx.new_key("^helloTp");
            key.set("Hello world!")?;
            Ok(TransactionStatus::Ok)
        },
        "BATCH",
        &[],
    )
    .unwrap();
}

#[test]
fn test_tp_returning_non_ydb_error() {
    let ctx = Context::new();
    let f = |_| {
        // We expect this to have an error
        String::from("Hello world!").parse::<u64>()?;
        Ok(TransactionStatus::Ok)
    };
    let result = ctx.tp(f, "BATCH", &[]);
    assert!(result.is_err());
    assert!(result.err().unwrap().is::<ParseIntError>());
}

#[test]
fn ydb_delete_excl_st() {
    let ctx = Context::new();
    ctx.write_lock();
    let mut key = KeyContext::variable(&ctx, "contextDeleteExcl");

    // Set a few values
    key.set(b"some value").unwrap();
    key.variable = "contextDeleteExcl2".into();
    key.set(b"some value").unwrap();

    // Delete `contextDeleteExcl2`, saving `contextDeleteExcl`
    key.context.delete_excl(&["contextDeleteExcl"]).unwrap();
    // Check data
    let data_type = key.data().unwrap();
    assert_eq!(data_type, DataReturn::NoData);
    key.variable = "contextDeleteExcl".into();
    let data_type = key.data().unwrap();
    assert_eq!(data_type, DataReturn::ValueData);

    // Delete `contextDeleteExcl`
    key.context.delete_excl(&[]).unwrap();
    // Make sure it was actually deleted
    let data_type = key.data().unwrap();
    assert_eq!(data_type, DataReturn::NoData);

    // Saving a global/intrinsic variable should be an error
    use crate::craw::YDB_ERR_INVVARNAME;
    let err = key.context.delete_excl(&["^global"]).unwrap_err();
    assert_eq!(err.status, YDB_ERR_INVVARNAME);
    let err = ctx.delete_excl(&["$ZSTATUS"]).unwrap_err();
    assert_eq!(err.status, YDB_ERR_INVVARNAME);

    // Saving a variable that doesn't exist should do nothing and return YDB_OK.
    ctx.delete_excl(&["local"]).unwrap();
}

#[test]
fn lock_incr_st() {
    use std::time::Duration;
    let ctx = Context::new();
    let key = KeyContext::variable(&ctx, "contextIncrSt");

    key.lock_incr(Duration::from_secs(0)).unwrap();
    key.lock_incr(Duration::from_secs(0)).unwrap();
    key.lock_decr().unwrap();
    key.lock_decr().unwrap();
}

#[test]
fn get_and_parse() {
    let ctx = Context::new();
    let key = ctx.new_key("hello");
    key.set(1.651e12.to_string()).unwrap();
    let _: f64 = key.get_and_parse().unwrap();
    key.set("127.0.0.1").unwrap();
    let _: std::net::IpAddr = key.get_and_parse().unwrap();
    key.delete(DeleteType::DelNode).unwrap();
}
#[test]
fn get_and_parse_tp() {
    let ctx = Context::new();
    let func = |ctx| {
        let _: usize = KeyContext::variable(ctx, "getParseTp").get_and_parse()?;
        panic!();
    };
    let err = ctx.tp(func, "BATCH", &[]).unwrap_err();
    let ydb_err = match *err.downcast::<ParseError<<usize as FromStr>::Err>>().unwrap() {
        ParseError::YDB(ydb) => ydb,
        _ => panic!(),
    };
    assert_eq!(ydb_err.status, crate::craw::YDB_ERR_LVUNDEF);
}
#[test]
fn prev_node_self() -> Result<(), Box<dyn Error>> {
    let ctx = Context::new();
    let mut key = make_ckey!(ctx, "^helloPrevNode", "0", "0");

    key.set("Hello world!")?;
    // Forget the second subscript
    key.truncate(1);
    // Go to the next node, then walk backward
    key[0] = Vec::from("1");
    key.prev_node_self()?;

    dbg!(&key);
    assert_eq!(key[1], b"0");

    Ok(())
}
#[test]
fn empty_subscripts() {
    let mut key = make_ckey!(Context::new(), "contextHello", "world");
    key.set("data").unwrap();
    key[0].clear();
    key.next_node_self().unwrap();
    assert_eq!(&key.get().unwrap(), b"data");
    assert_eq!(&key[0], b"world");
}
#[test]
fn no_subscripts() {
    let ctx = Context::new();
    let next = KeyContext::new(&ctx, "empty", &["subscript"]);
    next.set("some data").unwrap();
    let mut key = KeyContext::variable(&ctx, "empty");
    key.next_node_self().unwrap();
}

#[test]
fn ydb_lock_st() {
    use crate::simple_api::tests::lock_count;

    // Test `Context::lock`
    let ctx = Context::new();
    // This test cannot run in parallel with any others.
    ctx.write_lock();
    let key = KeyContext::variable(&ctx, "ydbCtxLock");
    assert_eq!(lock_count(&key.variable), 0);
    // Acquuire the lock
    ctx.lock(Duration::from_secs(1), std::slice::from_ref(&key.key)).unwrap();
    assert_eq!(lock_count(&key.variable), 1);
    // Release all locks
    ctx.lock(Duration::from_secs(1), &[]).unwrap();
    assert_eq!(lock_count(&key.variable), 0);
}

#[test]
fn architecture_example() {
    let mut key = Key::variable("^hello");
    key.push(b"world".to_vec());
    key[0] = b"Philadelphia".to_vec();
    assert_eq!(key, Key::new("^hello", &["Philadelphia"]));
}
