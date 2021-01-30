/****************************************************************
*                                                               *
* Copyright (c) 2020-2021 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

use std::ffi::CStr;

use crate::{YDBResult, simple_api::call_in::*};
use super::Context;

/// Call-in functions
impl Context {
    /// Open the call-in table stored in `file` and return its file descriptor.
    ///
    /// You can later switch the active call-in table by calling [`ci_tab_switch`] with the file descriptor.
    ///
    /// # See also
    /// - [C SimpleAPI documentation](https://docs.yottadb.com/MultiLangProgGuide/cprogram.html#ydb-ci-tab-open-ydb-ci-tab-open-t)
    /// - [Call-in interface](https://docs.yottadb.com/ProgrammersGuide/extrout.html#call-in-interface)
    /// - [`ci_t!`] and [`cip_t!`]
    ///
    /// # Errors

    // See `simple_api` for why this never returns PARAMINVALID

    /// - a negative [error return code] (for example, if the call-in table in the file had parse errors).
    ///
    /// [`ci_tab_switch`]: Context::ci_tab_switch()
    /// [error return code]: https://docs.yottadb.com/MessageRecovery/errormsgref.html#zmessage-codes
    ///
    /// # Example
    /// ```
    /// # fn main() -> yottadb::YDBResult<()> {
    /// use std::ffi::CString;
    /// use yottadb::context_api::Context;
    ///
    /// let ctx = Context::new();
    /// let file = CString::new("examples/m-ffi/calltab.ci").unwrap();
    /// let descriptor = ctx.ci_tab_open(&file)?;
    /// # Ok(())
    /// # }
    pub fn ci_tab_open(&self, file: &CStr) -> YDBResult<CallInTableDescriptor> {
        let tptoken = self.tptoken();
        let buffer = self.take_buffer();
        let (descriptor, buffer) = ci_tab_open_t(tptoken, buffer, file)?;
        *self.context.buffer.borrow_mut() = buffer;
        Ok(descriptor)
    }
    /// Switch the active call-in table to `new_handle`. Returns the previously active table.
    ///
    /// `new_handle` is a file descriptor returned by [`ci_tab_open`].
    ///
    /// # Errors

    // See docs for `simple_api` for why we never return `PARAMINVALID`.

    /// - [a negative error return code](https://docs.yottadb.com/MessageRecovery/errormsgref.html#standard-error-codes)
    ///
    /// [`ci_tab_open`]: Context::ci_tab_open()
    ///
    /// # Example
    /// ```
    /// # fn main() -> yottadb::YDBResult<()> {
    /// use std::ffi::CString;
    /// use yottadb::context_api::Context;
    ///
    /// let ctx = Context::new();
    /// let file = CString::new("examples/m-ffi/calltab.ci").unwrap();
    /// let descriptor = ctx.ci_tab_open(&file)?;
    /// let old_ci_table = ctx.ci_tab_switch(descriptor)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn ci_tab_switch(
        &self, new_handle: CallInTableDescriptor,
    ) -> YDBResult<CallInTableDescriptor> {
        let tptoken = self.tptoken();
        let buffer = self.take_buffer();
        let (descriptor, buffer) = ci_tab_switch_t(tptoken, buffer, new_handle)?;
        *self.context.buffer.borrow_mut() = buffer;
        Ok(descriptor)
    }
}
