//! Provides a Rust-interface for YottaDB which hides some of the complexity related to
//! managing error-return buffers and tptokens.
//!
//! Most operations are encapsulated in methods in the KeyContext struct. In addition
//! to easier-to-use get/set/delete/data, iteration helpers are available to iterate
//! over values in the database in a variety of ways.
//!
//! # Examples
//!
//! A basic database operation (set a value, retrieve it, and delete it)
//!
//! ```
//! # #[macro_use] extern crate yottadb;
//! use yottadb::craw::YDB_NOTTP;
//! use yottadb::context_api::Context;
//! use yottadb::simple_api::{DeleteType, YDBResult};
//!
//! fn main() -> YDBResult<()> {
//!     let ctx = Context::new();
//!     let mut key = make_ckey!(ctx, "^MyGlobal", "SubscriptA", "42");
//!     let value = Vec::from("This is a persistent message");
//!     key.set(&value)?;
//!     let buffer = key.get()?;
//!     assert_eq!("This is a persistent message", String::from_utf8_lossy(&buffer));
//!     key.delete(DeleteType::DelNode)?;
//!     Ok(())
//! }
//! ```
//!
use std::cell::RefCell;
use std::error::Error;
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
                    Err(YDBError { status: YDB_ERR_NODEEND, .. }) => None,
                    Err(x) => Some(Err(x)),
                }
            }
        }
    }
}

macro_rules! gen_iter_proto {
    ($(#[$meta:meta])*
     $name:ident, $return_type:tt) => {
        $(#[$meta])*
            pub fn $name(&mut self) -> $return_type {
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

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
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

    pub fn tp(&mut self, f: &mut dyn FnMut(&mut Context) -> Result<(), Box<dyn Error>>, trans_id: &str,
    locals_to_reset: &[Vec<u8>]) -> Result<(), Box<dyn Error>> {

        let tptoken = self.context.borrow().tptoken;
        // allocate a new buffer for errors, since we need context.buffer to pass `self` to f
        let result = tp_st(tptoken, Vec::with_capacity(1024), &mut |tptoken: u64| {
            self.context.borrow_mut().tptoken = tptoken;
            f(self)
        }, trans_id, locals_to_reset);
        self.context.borrow_mut().tptoken = tptoken;
        // discard the new buffer
        result.map(|_| {})
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
    /// Gets the value of this key from the database and returns the value.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_GVUNDEF, YDB_ERR_INVSVN, YDB_ERR_LVUNDEF as appropriate if no such variable or node exists
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     let output_buffer = key.get()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&output_buffer), "Hello world!");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn get(&mut self) -> YDBResult<Vec<u8>> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = Vec::with_capacity(1024);
        if self.context.borrow().multithreaded {
            self.key.get_st(tptoken, out_buffer)
        } else {
            panic!("Not supported!")
        }
    }

    /// Sets the value of a key in the database.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_INVSVN if no such intrinsic special variable exists
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn set(&mut self, new_val: &[u8]) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = if self.context.borrow().multithreaded {
            self.key.set_st(tptoken, out_buffer, &new_val)
        } else {
            panic!("Not supported!");
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

    /// Retuns the following information in DataReturn about a local or global variable node:
    ///
    /// * NoData: There is neither a value nor a subtree; i.e it is undefined.
    /// * ValueData: There is a value, but no subtree.
    /// * TreeData: There is no value, but there is a subtree.
    /// * ValueTreeData: There are both a value and a subtree.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::simple_api::DataReturn;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^helloDoesNotExist");
    ///
    ///     assert_eq!(key.data()?, DataReturn::NoData);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn data(&mut self) -> YDBResult<DataReturn> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = if self.context.borrow().multithreaded {
            self.key.data_st(tptoken, out_buffer)
        } else {
            panic!("Not supported!");
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

    /// Delete nodes in the local or global variable tree or subtree specified. A value of DelNode or DelTree for DeleteType 
    /// specifies whether to delete just the node at the root, leaving the (sub)tree intact, or to delete the node as well as the (sub)tree.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use yottadb::simple_api::{DataReturn, DeleteType};
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^helloDeleteMe");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key.delete(DeleteType::DelTree)?;
    ///
    ///     assert_eq!(key.data()?, DataReturn::NoData);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn delete(&mut self, delete_type: DeleteType) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = if self.context.borrow().multithreaded {
            self.key.delete_st(tptoken, out_buffer, delete_type)
        } else {
            panic!("Not supported!");
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

    /// Converts the value to a [number](https://docs.yottadb.com/MultiLangProgGuide/programmingnotes.html#canonical-numbers) and increments it based on the value specifed by Option. It defaults to 1 if the value is NULL.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NUMOFLOW
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^helloIncrementMe");
    ///
    ///     key.set(&Vec::from("0"))?;
    ///     key.increment(None)?;
    ///     let output_buffer = key.get()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&output_buffer), "1");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn increment(&mut self, increment: Option<&Vec<u8>>) -> YDBResult<Vec<u8>> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = Vec::with_capacity(1024);
        if self.context.borrow().multithreaded {
            self.key.incr_st(tptoken, out_buffer, increment)
        } else {
            panic!("Not supported!");
        }
    }

    /// Implements breadth-first traversal of a tree by searching for the next subscript, and passes itself in as the output parameter.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key[1] = Vec::from("1");
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key[1] = Vec::from("0");
    ///     key.next_sub_self()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&key[1]), "1");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn next_sub_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = if self.context.borrow().multithreaded {
            self.key.sub_next_self_st(tptoken, out_buffer)
        } else {
            panic!("Not supported!");
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
    /// Implements reverse breadth-first traversal of a tree by searching for the previous subscript, and passes itself in as the output parameter.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key[1] = Vec::from("1");
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key[1] = Vec::from("1");
    ///     key.prev_sub_self()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&key[1]), "0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn prev_sub_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = if self.context.borrow().multithreaded {
            self.key.sub_prev_self_st(tptoken, out_buffer)
        } else {
            panic!("Not supported!");
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

    /// Implements breadth-first traversal of a tree by searching for the next subscript.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key[1] = Vec::from("1");
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key[1] = Vec::from("0");
    ///     let k2 = key.next_sub()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&k2[1]), "1");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn next_sub(&mut self) -> YDBResult<KeyContext> {
        let mut ret = self.clone();
        ret.next_sub_self()?;
        Ok(ret)
    }

    /// Implements reverse breadth-first traversal of a tree by searching for the previous subscript.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key[1] = Vec::from("1");
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     key[1] = Vec::from("1");
    ///     let k2 = key.prev_sub()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&k2[1]), "0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn prev_sub(&mut self) -> YDBResult<KeyContext> {
        let mut ret = self.clone();
        ret.prev_sub_self()?;
        Ok(ret)
    }

    /// Facilitates depth-first traversal of a local or global variable tree, and passes itself in as the output parameter.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0", "0");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     // Forget the second subscript
    ///     unsafe {
    ///         key.set_len(2);
    ///     }
    ///     key.next_node_self()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&key[2]), "0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn next_node_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = if self.context.borrow().multithreaded {
            self.key.node_next_self_st(tptoken, out_buffer)
        } else {
            panic!("Not supported!");
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

    /// Facilitates reverse depth-first traversal of a local or global variable tree and reports the predecessor node, passing itself in as the output parameter.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0", "0");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     // Forget the second subscript
    ///     unsafe {
    ///         key.set_len(2);
    ///     }
    ///     // Go to the next node, then walk backward
    ///     key[1] = Vec::from("1");
    ///     key.prev_node_self()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&key[2]), "0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn prev_node_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = if self.context.borrow().multithreaded {
            self.key.node_prev_self_st(tptoken, out_buffer)
        } else {
            panic!("Not supported!");
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

    /// Facilitate depth-first traversal of a local or global variable tree.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0", "0");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     // Forget the second subscript
    ///     unsafe {
    ///         key.set_len(2);
    ///     }
    ///     let k2 = key.next_node()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&k2[2]), "0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn next_node(&mut self) -> YDBResult<KeyContext> {
        let mut ret = self.clone();
        ret.next_node_self()?;
        Ok(ret)
    }

    /// Facilitates reverse depth-first traversal of a local or global variable tree, and returns
    /// the previous node.
    ///
    /// # Errors
    ///
    /// Possible errors for this function include:
    /// - YDB_ERR_NODEEND
    /// - [error return codes](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate yottadb;
    /// use yottadb::context_api::Context;
    /// use std::error::Error;
    ///
    /// fn main() -> Result<(), Box<Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^helloPrevNode", "0", "0");
    ///
    ///     key.set(&Vec::from("Hello world!"))?;
    ///     // Forget the second subscript
    ///     unsafe {
    ///         key.set_len(2);
    ///     }
    ///     // Go to the next node, then walk backward
    ///     key[1] = Vec::from("1");
    ///     let k2 = key.prev_node()?;
    ///
    ///     assert_eq!(String::from_utf8_lossy(&k2[2]), "0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn prev_node(&mut self) -> YDBResult<KeyContext> {
        let mut ret = self.clone();
        ret.prev_node_self()?;
        Ok(ret)
    }

    gen_iter_proto!(
        /// Iterates over all the values at this level of the database tree and returns the value for
        /// each node.
        iter_values, ForwardValueIterator
        );

    gen_iter_proto!(
        /// Iterates over all the subscripts at this level of the database tree and returns the
        /// subscript for each node.
        iter_subs, ForwardSubIterator
        );

    gen_iter_proto!(
        /// Iterates over all the subscripts at this level of the database tree and returns the subscript and value for each node.
        iter_subs_values, ForwardSubValueIterator
        );

    gen_iter_proto!(
        /// Iterates over all subscripts at this level of the database tree and returns a copy of the key at each subscript.
        iter_key_subs, ForwardKeySubIterator
        );

    gen_iter_proto!(
        /// Iterates over all nodes for the global pointed to by the key and returns the value at each node.
        iter_nodes, ForwardNodeIterator
        );

    gen_iter_proto!(
        /// Iterates over all nodes for the global pointed to by the key and returns a copy of the key at each node.
        iter_key_nodes, ForwardKeyNodeIterator
        );

    gen_iter_proto!(
        /// Iterates in reverse order over all the values at this level of the database tree and returns the value for
        /// each node.
        iter_values_reverse, ReverseValueIterator
        );

    gen_iter_proto!(
        /// Iterates in reverse order over all the subscripts at this level of the database tree and returns the
        /// subscript for each node.
        iter_subs_reverse, ReverseSubIterator
        );

    gen_iter_proto!(
        /// Iterates in reverse order over all the subscripts at this level of the database tree and returns the subscript and value for each node.
        iter_subs_values_reverse, ReverseSubValueIterator
        );

    gen_iter_proto!(
        /// Iterates in reverse order over all subscripts at this level of the database tree and returns a copy of the key at each subscript.
        iter_key_subs_reverse, ReverseKeySubIterator
        );

    gen_iter_proto!(
        /// Iterates in reverse order over all nodes for the global pointed to by the key and returns the value at each node.
        iter_nodes_reverse, ReverseNodeIterator
        );

    gen_iter_proto!(
        /// Iterates in reverse oder over all nodes for the global pointed to by the key and returns a copy of the key at each node.
        iter_key_nodes_reverse, ReverseKeyNodeIterator
        );
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
        let err = val.err().unwrap();
        return Some(Err(err));
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
        let err = val.err().unwrap();
        return Some(Err(err));
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
    use std::num::ParseIntError;

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

    #[test]
    fn simple_prev_node() {
        let ctx = Context::new();
        let mut key = make_ckey!(ctx, "^hello", "0", "0");

        key.set(&Vec::from("Hello world!")).unwrap();
        // Forget the second subscript
        unsafe {
            key.set_len(2);
        }
        // Go to the next node, then walk backward
        key[1] = Vec::from("1");
        let k2 = key.prev_node().unwrap();

        assert_eq!(String::from_utf8_lossy(&k2[2]), "0");
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
                    }, "Values don't match on {}th iteration", i);
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
            key.set(&Vec::from("Hello world!"))?;
            Ok(())
        }, "BATCH", &Vec::new()).unwrap();
    }

    #[test]
    fn test_tp_returning_non_ydb_error() {
        let mut ctx = Context::new();
        let result = ctx.tp(&mut |_ctx: &mut Context| {
            // We expect this to have an error
            String::from("Hello world!").parse::<u64>()?;
            Ok(())
        }, "BATCH", &Vec::new());
        assert!(result.is_err());
        assert!(result.err().unwrap().is::<ParseIntError>());
    }
}
