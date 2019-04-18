use std::cell::RefCell;
use std::rc::Rc;
use std::ops::{Deref, DerefMut};

use crate::craw::{YDB_NOTTP, YDB_ERR_NODEEND};
use crate::simple_api::{tp_st, Key, YDBResult, YDBError, DataReturn, DeleteType};

// Private macro to help make iterators
macro_rules! implement_iterator {
    ($name:ident, $advance:ident, $return_type:ty, $next:expr) => {
        pub struct $name<'a> {
            key: &'a mut KeyContext,
        }

        impl<'a> Iterator for $name<'a> {
            type Item = YDBResult<$return_type>;

            fn next(&mut self) -> Option<Self::Item> {
                match self.key.$advance() {
                    Ok(_) => {
                        $next(self)
                    },
                    Err(YDBError(x, y)) => match y {
                        YDB_ERR_NODEEND => None,
                        _ => panic!(YDBError(x, y)),
                    }
                }
            }
        }
    }
}

macro_rules! gen_iter_proto {
    ($name:ident, $return_type:tt) => {
        pub fn $name<'a>(&'a mut self) -> $return_type<'a> {
            $return_type {
                key: self,
            }
        }
    }
}


/// Create a KeyContext with the given subscripts, provided a context.
///
/// # Examples
///
/// ```
/// # #[macro_use] extern crate yottadb;
/// use std::error::Error;
/// use yottadb::context_api::Context;
///
/// fn main() -> Result<(), Box<Error>> {
///     let mut ctx = Context::new();
///     let mut key = make_ckey!(ctx, "^hello", "world");
///     key.data()?;
///
///     Ok(())
/// }
/// ```
#[macro_export]
macro_rules! make_ckey {
    ( $ctx:expr, $gbl:expr $(, $x:expr)* ) => ({
        let mut key = $ctx.new_key();
        key.push(Vec::from($gbl));
        $(
            key.push(Vec::from($x));
        )*
        key
    })
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct ContextInternal {
    buffer: Option<Vec<u8>>,
    tptoken: u64,
    multithreaded: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context {
    context: Rc<RefCell<ContextInternal>>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct KeyContext {
    context: Rc<RefCell<ContextInternal>>,
    pub(crate) key: Key,
}

impl Context {
    pub fn new() -> Context {
        Context{
            context: Rc::new(RefCell::new(ContextInternal {
                buffer: Some(Vec::with_capacity(1024)),
                tptoken: YDB_NOTTP,
                multithreaded: true,
            }))
        }
    }

    pub fn new_key(&self) -> KeyContext {
        KeyContext {
            context: self.context.clone(),
            key: Key::with_capacity(32),
        }
    }

    pub fn tp(&mut self, f: &mut FnMut(&mut Context) -> YDBResult<()>, trans_id: &str,
        locals_to_reset: &[Vec<u8>]) -> YDBResult<()> {

        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = tp_st(tptoken, out_buffer, &mut |tptoken: u64, new_buffer: Vec<u8>| {
            self.context.borrow_mut().tptoken = tptoken;
            self.context.borrow_mut().buffer = Some(new_buffer);
            match f(self) {
                Ok(()) => {
                    let buff = self.context.borrow_mut().buffer.take().unwrap();
                    Ok(buff)
                },
                Err(x) => {
                    Err(x)
                }
            }
        }, trans_id, locals_to_reset);
        self.context.borrow_mut().tptoken = tptoken;
        match result {
            Ok(x) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(())
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            }
        }
    }
}

impl Deref for KeyContext {
    type Target = Vec<Vec<u8>>;

    fn deref(&self) -> &Self::Target {
        &self.key.buffers
    }
}

impl DerefMut for KeyContext {
    fn deref_mut(&mut self) -> &mut Vec<Vec<u8>> {
        self.key.needs_sync = true;
        &mut self.key.buffers
    }
}

impl KeyContext {
    pub fn get(&mut self) -> YDBResult<Vec<u8>> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = Vec::with_capacity(1024);
        match self.context.borrow().multithreaded {
            _ => self.key.get_st(tptoken, out_buffer)
        }
    }

    pub fn set(&mut self, new_val: &Vec<u8>) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = match self.context.borrow().multithreaded {
            _ => self.key.set_st(tptoken, out_buffer, &new_val)
        };
        match result {
            Ok(x) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(())
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            },
        }
    }

    pub fn data(&mut self) -> YDBResult<DataReturn> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = match self.context.borrow().multithreaded {
            _ => self.key.data_st(tptoken, out_buffer)
        };
        match result {
            Ok((y, x)) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(y)
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            },
        }
    }

    pub fn delete(&mut self, delete_type: DeleteType) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = match self.context.borrow().multithreaded {
            _ => self.key.delete_st(tptoken, out_buffer, delete_type)
        };
        match result {
            Ok(x) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(())
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            },
        }
    }

    pub fn increment(&mut self, increment: Option<&Vec<u8>>) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = match self.context.borrow().multithreaded {
            _ => self.key.incr_st(tptoken, out_buffer, increment)
        };
        match result {
            Ok(x) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(())
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            },
        }
    }

    pub fn next_sub_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = match self.context.borrow().multithreaded {
            _ => self.key.sub_next_self_st(tptoken, out_buffer)
        };
        match result {
            Ok(x) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(())
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            },
        }
    }
    pub fn prev_sub_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = match self.context.borrow().multithreaded {
            _ => self.key.sub_prev_self_st(tptoken, out_buffer)
        };
        match result {
            Ok(x) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(())
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            },
        }
    }

    pub fn next_sub(&mut self) -> YDBResult<KeyContext> {
        let mut ret = self.clone();
        ret.next_sub_self()?;
        Ok(ret)
    }

    pub fn prev_sub(&mut self) -> YDBResult<KeyContext> {
        let mut ret = self.clone();
        ret.prev_sub_self()?;
        Ok(ret)
    }

    pub fn next_node_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = match self.context.borrow().multithreaded {
            _ => self.key.node_next_self_st(tptoken, out_buffer)
        };
        match result {
            Ok(x) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(())
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            },
        }
    }

    pub fn prev_node_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = match self.context.borrow().multithreaded {
            _ => self.key.node_prev_self_st(tptoken, out_buffer)
        };
        match result {
            Ok(x) => {
                self.context.borrow_mut().buffer = Some(x);
                Ok(())
            },
            Err(x) => {
                self.context.borrow_mut().buffer = Some(Vec::with_capacity(1024));
                Err(x)
            },
        }
    }

    pub fn next_node(&mut self) -> YDBResult<KeyContext> {
        let mut ret = self.clone();
        ret.next_node_self()?;
        Ok(ret)
    }

    pub fn prev_node(&mut self) -> YDBResult<KeyContext> {
        let mut ret = self.clone();
        ret.prev_node_self()?;
        Ok(ret)
    }

    gen_iter_proto!(iter_values, ForwardValueIterator);
    gen_iter_proto!(iter_subs, ForwardSubIterator);
    gen_iter_proto!(iter_subs_values, ForwardSubValueIterator);
    gen_iter_proto!(iter_key_subs, ForwardKeySubIterator);
    gen_iter_proto!(iter_nodes, ForwardNodeIterator);
    gen_iter_proto!(iter_key_nodes, ForwardKeyNodeIterator);

    gen_iter_proto!(iter_values_reverse, ReverseValueIterator);
    gen_iter_proto!(iter_subs_reverse, ReverseSubIterator);
    gen_iter_proto!(iter_subs_values_reverse, ReverseSubValueIterator);
    gen_iter_proto!(iter_key_subs_reverse, ReverseKeySubIterator);
    gen_iter_proto!(iter_nodes_reverse, ReverseNodeIterator);
    gen_iter_proto!(iter_key_nodes_reverse, ReverseKeyNodeIterator);
}

implement_iterator!(ForwardValueIterator, next_sub_self, Vec<u8>, |me: &mut ForwardValueIterator| {
    Some(me.key.get())
});

implement_iterator!(ForwardSubIterator, next_sub_self, Vec<u8>, |me: &mut ForwardSubIterator| {
    Some(Ok(me.key.last().unwrap().clone()))
});

implement_iterator!(ForwardSubValueIterator, next_sub_self, (Vec<u8>, Vec<u8>), |me: &mut ForwardSubValueIterator| {
    let val = me.key.get();
    if val.is_err() {
        panic!(val);
    }
    Some(Ok((me.key.last().unwrap().clone(), val.unwrap())))
});

implement_iterator!(ForwardKeySubIterator, next_sub_self, KeyContext, |me: &mut ForwardKeySubIterator| {
    Some(Ok(me.key.clone()))
});

implement_iterator!(ForwardNodeIterator, next_node_self, Vec<u8>, |me: &mut ForwardNodeIterator| {
    let data = me.key.data().unwrap();
    if data != DataReturn::ValueData && data != DataReturn::ValueTreeData {
        return me.next();
    }
    Some(me.key.get())
});

implement_iterator!(ForwardKeyNodeIterator, next_node_self, KeyContext, |me: &mut ForwardKeyNodeIterator| {
    Some(Ok(me.key.clone()))
});

implement_iterator!(ReverseValueIterator, prev_sub_self, Vec<u8>, |me: &mut ReverseValueIterator| {
    Some(me.key.get())
});

implement_iterator!(ReverseSubIterator, prev_sub_self, Vec<u8>, |me: &mut ReverseSubIterator| {
    Some(Ok(me.key.last().unwrap().clone()))
});

implement_iterator!(ReverseSubValueIterator, prev_sub_self, (Vec<u8>, Vec<u8>), |me: &mut ReverseSubValueIterator| {
    let val = me.key.get();
    if val.is_err() {
        panic!(val);
    }
    Some(Ok((me.key.last().unwrap().clone(), val.unwrap())))
});

implement_iterator!(ReverseKeySubIterator, prev_sub_self, KeyContext, |me: &mut ReverseKeySubIterator| {
    Some(Ok(me.key.clone()))
});

implement_iterator!(ReverseNodeIterator, prev_node_self, Vec<u8>, |me: &mut ReverseNodeIterator| {
    Some(me.key.get())
});

implement_iterator!(ReverseKeyNodeIterator, prev_node_self, KeyContext, |me: &mut ReverseKeyNodeIterator| {
    Some(Ok(me.key.clone()))
});

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_get() {
        let ctx = Context::new();
        let mut key = ctx.new_key();
        key.push(Vec::from("^hello"));
        key.set(&Vec::from("Hello world!")).unwrap();
        key.get().unwrap();
    }

    #[test]
    fn simple_set() {
        let ctx = Context::new();
        let mut key = ctx.new_key();
        key.push(Vec::from("^hello"));
        key.set(&Vec::from("Hello world!")).unwrap();
    }

    #[test]
    fn simple_data() {
        let ctx = Context::new();
        let mut key = ctx.new_key();
        key.push(Vec::from("^hello"));
        key.data().unwrap();
    }

    #[test]
    fn simple_delete() {
        let ctx = Context::new();
        let mut key = ctx.new_key();
        key.push(Vec::from("^helloDeleteMe"));
        key.set(&Vec::from("Hello world!")).unwrap();
        key.delete(DeleteType::DelNode).unwrap();
    }

    #[test]
    fn simple_increment() {
        let ctx = Context::new();
        let mut key = ctx.new_key();
        key.push(Vec::from("^helloIncrementMe"));
        key.increment(None).unwrap();
    }

    // Macro to test ordered expressions
    macro_rules! make_loop_test {
        ($testname:ident, $func:ident, $transform:expr,
         $($pat:pat => $val:expr),*) => {
            #[test]
            fn $testname() {
                let ctx = Context::new();
                let mut key = ctx.new_key();
                key.push(Vec::from("^helloSubLoop"));
                key.push(Vec::from("shire"));
                key.set(&Vec::from("Tolkien")).unwrap();
                key[1] = Vec::from("mundus");
                key.set(&Vec::from("Elder Scrolls")).unwrap();
                key[1] = Vec::from("high garden");
                key.set(&Vec::from("Song of Ice and Fire")).unwrap();
                unsafe {
                    key[1].set_len(0);
                }
                for (i, x) in key.$func().enumerate() {
                    let x = x.unwrap();
                    let x = $transform(x.clone());
                    assert_eq!(x, match i {
                        $( $pat => $val ),*,
                        _ => panic!("Unexpected value: <{:#?}>", x),
                    }, "Values don't matter on {}th iteration", i);
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
        (String::from_utf8_lossy(&x[0]).into_owned(), String::from_utf8_lossy(&x[1]).into_owned())
    }, 
                0 => (String::from("^helloSubLoop"), String::from("high garden")),
                1 => (String::from("^helloSubLoop"), String::from("mundus")),
                2 => (String::from("^helloSubLoop"), String::from("shire"))
    );

    make_loop_test!(test_iter_nodes, iter_nodes, |x: Vec<u8>| {
        String::from_utf8_lossy(&x).into_owned()
    }, 
                0 => "Song of Ice and Fire",
                1 => "Elder Scrolls",
                2 => "Tolkien"
    );

    make_loop_test!(test_iter_key_nodes, iter_key_nodes, |x: KeyContext| {
        (String::from_utf8_lossy(&x[0]).into_owned(), String::from_utf8_lossy(&x[1]).into_owned())
    }, 
                0 => (String::from("^helloSubLoop"), String::from("high garden")),
                1 => (String::from("^helloSubLoop"), String::from("mundus")),
                2 => (String::from("^helloSubLoop"), String::from("shire"))
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
        (String::from_utf8_lossy(&x[0]).into_owned(), String::from_utf8_lossy(&x[1]).into_owned())
    }, 
                2 => (String::from("^helloSubLoop"), String::from("high garden")),
                1 => (String::from("^helloSubLoop"), String::from("mundus")),
                0 => (String::from("^helloSubLoop"), String::from("shire"))
    );

    make_loop_test!(test_iter_nodes_reverse, iter_nodes_reverse, |x: Vec<u8>| {
        String::from_utf8_lossy(&x).into_owned()
    }, 
                2 => "Song of Ice and Fire",
                1 => "Elder Scrolls",
                0 => "Tolkien"
    );

    make_loop_test!(test_iter_key_nodes_reverse, iter_key_nodes_reverse, |x: KeyContext| {
        (String::from_utf8_lossy(&x[0]).into_owned(), String::from_utf8_lossy(&x[1]).into_owned())
    }, 
                2 => (String::from("^helloSubLoop"), String::from("high garden")),
                1 => (String::from("^helloSubLoop"), String::from("mundus")),
                0 => (String::from("^helloSubLoop"), String::from("shire"))
    );

    #[test]
    fn test_simple_tp() {
        let mut ctx = Context::new();
        ctx.tp(&mut |ctx: &mut Context| {
            let mut key = ctx.new_key();
            key.push(Vec::from("^hello"));
            key.set(&Vec::from("Hello world!"))
        }, "BATCH", &Vec::new()).unwrap();
    }
}
