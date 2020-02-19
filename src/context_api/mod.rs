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
//! use yottadb::context_api::Context;
//! use yottadb::{YDB_NOTTP, DeleteType, YDBResult};
//!
//! fn main() -> YDBResult<()> {
//!     let ctx = Context::new();
//!     let mut key = make_ckey!(ctx, "^MyGlobal", "SubscriptA", "42");
//!     let value = "This is a persistent message";
//!     key.set(value)?;
//!     let buffer = key.get()?;
//!     assert_eq!(&buffer, b"This is a persistent message");
//!     key.delete(DeleteType::DelNode)?;
//!     Ok(())
//! }
//! ```
//!
use std::cell::RefCell;
use std::error::Error;
use std::rc::Rc;
use std::str::FromStr;
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


/// Create a [`KeyContext`](context_api/struct.KeyContext.html) with the given subscripts, provided a context.
///
/// # Examples
///
/// ```
/// use std::error::Error;
/// use yottadb::context_api::Context;
///
/// fn main() -> Result<(), Box<Error>> {
///     let mut ctx = Context::new();
///     let mut key = yottadb::make_ckey!(ctx, "^hello", "world");
///     key.data()?;
///
///     Ok(())
/// }
/// ```
#[macro_export]
macro_rules! make_ckey {
    ( $ctx:expr, $var:expr $(,)?) => (
        $ctx.new_key($crate::simple_api::Key::variable($var))
    );
    ( $ctx:expr, $gbl:expr $(, $x:expr)+ ) => (
        $ctx.new_key(
            $crate::make_key!( $gbl, $($x),+ )
        )
    );
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct ContextInternal {
    buffer: Option<Vec<u8>>,
    tptoken: u64,
}

/// `Context` is _not_ thread-safe, async-safe, or re-entrant.
///
/// Example:
///
/// ```compile_fail
/// # #[macro_use] extern crate yottadb;
/// extern crate tokio;
/// use yottadb::context_api::Context;
///
/// let ctx = Context::new();
/// let mut key1 = make_ckey!(ctx, "key1");
/// let mut key2 = make_ckey!(ctx, "key2");
/// tokio::spawn(async {
///     ctx.tp(|_| Ok(()), "BATCH", &[])
/// });
/// ```
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
    context: Context,
    pub key: Key,
}

use core::cell::{Ref, RefMut};
impl Context {
    pub fn new() -> Context {
        Context{
            context: Rc::new(RefCell::new(ContextInternal {
                buffer: Some(Vec::with_capacity(1024)),
                tptoken: YDB_NOTTP,
            }))
        }
    }

    pub fn new_key<K: Into<Key>>(&self, key: K) -> KeyContext {
        KeyContext::with_key(self, key)
    }

    pub fn tp<'a, F>(&'a self, mut f: F, trans_id: &str, locals_to_reset: &[Vec<u8>])
            -> Result<(), Box<dyn Error>>
            where F: FnMut(&'a Self) -> Result<(), Box<dyn Error>> {

        let tptoken = self.context.borrow().tptoken;
        // allocate a new buffer for errors, since we need context.buffer to pass `self` to f
        let result = tp_st(tptoken, Vec::with_capacity(50), |tptoken: u64| {
            self.context.borrow_mut().tptoken = tptoken;
            f(self)
        }, trans_id, locals_to_reset);
        self.context.borrow_mut().tptoken = tptoken;
        // discard the new buffer
        result.map(|_| {})
    }

    /// Delete all local variables _except_ for those passed in `saved_variable`.
    ///
    /// Passing an empty `saved_variables` slice deletes all local variables.
    /// Attempting to save a global or intrinsic variable is an error.
    ///
    /// # Errors
    /// - YDB_ERR_NAMECOUNT2HI if `saved_variables.len() > YDB_MAX_NAMES`
    /// - YDB_ERR_INVVARNAME if attempting to save a global or intrinsic variable
    /// - Another system [error return code](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#error-return-code)
    ///
    /// # See also
    /// - The [Simple API documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-delete-excl-s-ydb-delete-excl-st)
    /// - [Local and global variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#local-and-global-variables)
    /// - [Instrinsic special variables](https://docs.yottadb.com/MultiLangProgGuide/MultiLangProgGuide.html#intrinsic-special-variables)
    pub fn delete_excl(&self, saved_variables: &[&str]) -> YDBResult<()> {
        use crate::simple_api::delete_excl_st;

        let tptoken = self.context.borrow().tptoken;
        let result = delete_excl_st(tptoken, self.context.borrow_mut().buffer.take().unwrap(), saved_variables);
        self.recover_buffer(result)
    }
    fn recover_buffer(&self, result: YDBResult<Vec<u8>>) -> YDBResult<()> {
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
    fn borrow(&self) -> Ref<'_, ContextInternal> {
        self.context.borrow()
    }
    fn borrow_mut(&self) -> RefMut<'_, ContextInternal> {
        self.context.borrow_mut()
    }
}

impl Deref for KeyContext {
    type Target = Key;

    fn deref(&self) -> &Self::Target {
        &self.key
    }
}

impl DerefMut for KeyContext {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.key
    }
}

impl From<(&Context, Key)> for KeyContext {
    fn from((ctx, key): (&Context, Key)) -> Self {
        KeyContext::with_key(ctx, key)
    }
}

/// The error type returned by `KeyContext::get_and_parse()`
#[derive(Debug)]
pub enum ParseError<T> {
    /// There was an error retrieving the value from the database.
    YDB(YDBError),
    /// Retrieving the value succeeded, but it was not a valid `String`.
    ///
    /// The bytes of the value are still available using `.into_bytes()`.
    Utf8(std::string::FromUtf8Error),
    /// A valid `String` was retrieved but did not parse successfully.
    /// The `String` is still available.
    ///
    /// The `T` is the type of `FromStr::Err` for the value being parsed.
    Parse(T, String),
}

impl KeyContext {
    // this should be kept in sync with `Key::new`
    pub fn new<V, S>(ctx: &Context, variable: V, subscripts: &[S]) -> KeyContext
            where V: Into<String>,
                  S: Into<Vec<u8>> + Clone, {
        Self::with_key(ctx, Key::new(variable, subscripts))
    }
    /// Shortcut for creating a key with no subscripts.
    // this should be kept in sync with `Key::variable`
    pub fn variable<V: Into<String>>(ctx: &Context, var: V) -> Self {
        Self::with_key(ctx, var)
    }
    pub fn with_key<K: Into<Key>>(ctx: &Context, key: K) -> Self {
        Self {
            context: ctx.clone(),
            key: key.into(),
        }
    }
    fn recover_buffer(&self, result: YDBResult<Vec<u8>>) -> YDBResult<()> {
        self.context.recover_buffer(result)
    }
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
    ///     key.set("Hello world!")?;
    ///     let output_buffer = key.get()?;
    ///
    ///     assert_eq!(output_buffer, b"Hello world!");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn get(&self) -> YDBResult<Vec<u8>> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = Vec::with_capacity(1024);
        self.key.get_st(tptoken, out_buffer)
    }

    /// Retrieve a value from the database and parse it into a Rust data structure.
    ///
    /// This is a shorthand for `String::from_utf8(key.get()).parse()`
    /// that collects the errors into a single enum.
    ///
    /// # Examples
    /// Set and retrieve an integer, with error handling.
    /// ```
    /// use yottadb::context_api::Context;
    /// use yottadb::context_api::ParseError;
    /// let ctx = Context::new();
    /// let mut key = ctx.new_key("weekday");
    /// key.set(5.to_string())?;
    /// let day: u8 = match key.get_and_parse() {
    ///     Ok(day) => day,
    ///     Err(ParseError::YDB(err)) => return Err(err),
    ///     Err(ParseError::Utf8(err)) => {
    ///         eprintln!("warning: had an invalid string");
    ///         String::from_utf8_lossy(&err.as_bytes()).parse().unwrap()
    ///     }
    ///     Err(ParseError::Parse(err, original)) => {
    ///         panic!("{} is not a valid string: {}", original, err);
    ///     }
    /// };
    /// Ok(())
    /// ```
    ///
    /// Set and retrieve an integer, without error handling.
    /// ```
    /// # use yottadb::simple_api::YDBResult;
    /// # fn main() -> YDBResult<()> {
    /// use yottadb::context_api::Context;
    /// let ctx = Context::new();
    /// let mut key = ctx.new_key("weekday");
    /// key.set(5.to_string())?;
    /// let day: u8 = key.get_and_parse().unwrap();
    /// Ok(())
    /// # }
    /// ```
    pub fn get_and_parse<T: FromStr>(&self) -> Result<T, ParseError<T::Err>> {
        self.get().map_err(ParseError::YDB)
            .and_then(|bytes| String::from_utf8(bytes).map_err(ParseError::Utf8))
            .and_then(|s| s.parse().map_err(|err| ParseError::Parse(err, s)))
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
    ///     key.set("Hello world!")?;
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn set<U: AsRef<[u8]>>(&self, new_val: U) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = self.key.set_st(tptoken, out_buffer, new_val);
        self.recover_buffer(result)
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
    pub fn data(&self) -> YDBResult<DataReturn> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        match self.key.data_st(tptoken, out_buffer) {
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
    ///     key.set("Hello world!")?;
    ///     key.delete(DeleteType::DelTree)?;
    ///
    ///     assert_eq!(key.data()?, DataReturn::NoData);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn delete(&self, delete_type: DeleteType) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = self.key.delete_st(tptoken, out_buffer, delete_type);
        self.recover_buffer(result)
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
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^helloIncrementMe");
    ///
    ///     key.set("0")?;
    ///     key.increment(None)?;
    ///     let output_buffer = key.get()?;
    ///     assert_eq!(output_buffer, b"1");
    ///
    ///     key.increment(Some(b"100"));
    ///     let output_buffer = key.get()?;
    ///     assert_eq!(output_buffer, b"101");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn increment(&self, increment: Option<&[u8]>) -> YDBResult<Vec<u8>> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = Vec::with_capacity(1024);
        self.key.incr_st(tptoken, out_buffer, increment)
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
    ///     key.set("Hello world!")?;
    ///     key[0] = Vec::from("1");
    ///     key.set("Hello world!")?;
    ///     key[0] = Vec::from("0");
    ///     key.next_sub_self()?;
    ///
    ///     assert_eq!(key[0], b"1");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn next_sub_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = self.key.sub_next_self_st(tptoken, out_buffer);
        self.recover_buffer(result)
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
    ///     key.set("Hello world!")?;
    ///     key[0] = Vec::from("1");
    ///     key.set("Hello world!")?;
    ///     key[0] = Vec::from("1");
    ///     key.prev_sub_self()?;
    ///
    ///     assert_eq!(key[0], b"0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn prev_sub_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = self.key.sub_prev_self_st(tptoken, out_buffer);
        self.recover_buffer(result)
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
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0");
    ///
    ///     key.set("Hello world!")?;
    ///     key[0] = Vec::from("1");
    ///     key.set("Hello world!")?;
    ///     key[0] = Vec::from("0");
    ///     let k2 = key.next_sub()?;
    ///
    ///     assert_eq!(&k2[0], b"1");
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
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0");
    ///
    ///     key.set(b"Hello world!")?;
    ///     key[0] = Vec::from("1");
    ///     key.set("Hello world!")?;
    ///     key[0] = Vec::from("1");
    ///     let k2 = key.prev_sub()?;
    ///
    ///     assert_eq!(&k2[0], b"0");
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
    ///     key.set("Hello world!")?;
    ///     // Forget the second subscript
    ///     key.truncate(1);
    ///     key.next_node_self()?;
    ///
    ///     assert_eq!(key[1], b"0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn next_node_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = self.key.node_next_self_st(tptoken, out_buffer);
        self.recover_buffer(result)
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
    ///     key.set("Hello world!")?;
    ///     // Forget the second subscript
    ///     key.truncate(1);
    ///     // Go to the next node, then walk backward
    ///     key[0] = Vec::from("1");
    ///     key.prev_node_self()?;
    ///
    ///     assert_eq!(key[1], b"0");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn prev_node_self(&mut self) -> YDBResult<()> {
        let tptoken = self.context.borrow().tptoken;
        let out_buffer = self.context.borrow_mut().buffer.take().unwrap();
        let result = self.key.node_prev_self_st(tptoken, out_buffer);
        self.recover_buffer(result)
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
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^hello", "0", "0");
    ///
    ///     key.set("Hello world!")?;
    ///     // Forget the second subscript
    ///     key.truncate(1);
    ///     let k2 = key.next_node()?;
    ///
    ///     assert_eq!(k2[1], b"0");
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
    /// fn main() -> Result<(), Box<dyn Error>> {
    ///     let ctx = Context::new();
    ///     let mut key = make_ckey!(ctx, "^helloPrevNode", "0", "0");
    ///
    ///     key.set("Hello world!")?;
    ///     // Forget the second subscript
    ///     key.truncate(1);
    ///     // Go to the next node, then walk backward
    ///     key[0] = "1".into();
    ///     let k2 = key.prev_node()?;
    ///
    ///     assert_eq!(&k2.variable, "^helloPrevNode");
    ///     assert_eq!(k2[0], b"0");
    ///     assert_eq!(k2[1], b"0");
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
        let key = ctx.new_key(Key::variable("^hello"));
        key.set(b"Hello world!").unwrap();
        assert_eq!(key.get().unwrap(), b"Hello world!");
        key.delete(DeleteType::DelNode).unwrap();
    }

    #[test]
    fn simple_set() {
        let ctx = Context::new();
        let key = ctx.new_key(Key::variable("^hello"));
        key.set(b"Hello world!").unwrap();
        key.set("Hello str!").unwrap();
        key.set(String::from("Hello String!")).unwrap();
        key.delete(DeleteType::DelNode).unwrap();
    }

    #[test]
    fn simple_data() {
        let ctx = Context::new();
        let key = ctx.new_key(Key::variable("^hello"));
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
        let mut key = make_ckey!(ctx, "^hello", "0", "0");

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
        ctx.tp(|ctx| {
            let key = ctx.new_key("^hello");
            key.set("Hello world!")?;
            Ok(())
        }, "BATCH", &[]).unwrap();
    }

    #[test]
    fn test_tp_returning_non_ydb_error() {
        let ctx = Context::new();
        let f = |_| {
            // We expect this to have an error
            String::from("Hello world!").parse::<u64>()?;
            Ok(())
        };
        let result = ctx.tp(f, "BATCH", &[]);
        assert!(result.is_err());
        assert!(result.err().unwrap().is::<ParseIntError>());
    }

    #[test]
    fn ydb_delete_excl_st() {
        let ctx = Context::new();
        let mut key = KeyContext::variable(&ctx, "deleteExcl");

        // Set a few values
        key.set(b"some value").unwrap();
        key.variable = "deleteExcl2".into();
        key.set(b"some value").unwrap();

        // Delete `deleteExcl2`, saving `deleteExcl`
        key.context.delete_excl(&["deleteExcl"]).unwrap();
        // Check data
        let data_type = key.data().unwrap();
        assert_eq!(data_type, DataReturn::NoData);
        key.variable = "deleteExcl".into();
        let data_type = key.data().unwrap();
        assert_eq!(data_type, DataReturn::ValueData);

        // Delete `deleteExcl`
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
    fn prev_node_self() -> Result<(), Box<dyn Error>> {
        let ctx = Context::new();
        let mut key = make_ckey!(ctx, "^hello", "0", "0");

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
        let next = KeyContext::new(&Context::new(), "empty", &["subscript"]);
        next.set("some data").unwrap();
        let mut key = KeyContext::variable(&Context::new(), "empty");
        key.next_node_self().unwrap();
    }
}
