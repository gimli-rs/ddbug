use std::cmp;
use std::collections::BinaryHeap;
use std::io::Write;
use std::usize;

use parser::FileHash;

use crate::code::Code;
use crate::{Options, Result};

mod text;
pub use self::text::TextPrinter;

mod html;
pub use self::html::HtmlPrinter;

pub(crate) mod base_type;
pub(crate) mod enumeration;
pub(crate) mod file;
pub(crate) mod frame_location;
pub(crate) mod function;
pub(crate) mod inherit;
pub(crate) mod inlined_function;
pub(crate) mod local_variable;
pub(crate) mod member;
pub(crate) mod namespace;
pub(crate) mod parameter;
pub(crate) mod range;
pub(crate) mod register;
pub(crate) mod section;
pub(crate) mod source;
pub(crate) mod struct_type;
pub(crate) mod symbol;
pub(crate) mod type_def;
pub(crate) mod types;
pub(crate) mod union_type;
pub(crate) mod unit;
pub(crate) mod variable;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum DiffPrefix {
    None,
    Equal,
    Delete,
    Add,
    Modify,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Id {
    Unit {
        unit_index: usize,
    },
    Type {
        unit_index: usize,
        type_index: usize,
    },
    Function {
        unit_index: usize,
        function_index: usize,
    },
    Variable {
        unit_index: usize,
        variable_index: usize,
    },
}

pub trait Printer {
    fn value(
        &mut self,
        buf: &mut Vec<u8>,
        f: &mut dyn FnMut(&mut dyn ValuePrinter) -> Result<()>,
    ) -> Result<()>;

    /// Calls `f` to write to a temporary buffer.
    fn buffer(
        &mut self,
        buf: &mut Vec<u8>,
        f: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
    ) -> Result<()>;
    fn write_buf(&mut self, buf: &[u8]) -> Result<()>;

    fn line_break(&mut self) -> Result<()>;

    fn line(&mut self, label: &str, buf: &[u8]) -> Result<()>;
    fn line_diff(&mut self, id: usize, label: &str, a: &[u8], b: &[u8]) -> Result<()>;

    fn indent_body(
        &mut self,
        buf: &mut Vec<u8>,
        body: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
    ) -> Result<()>;
    fn indent_header(
        &mut self,
        collapsed: bool,
        body: &[u8],
        header: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
    ) -> Result<()>;
    fn indent_id(
        &mut self,
        id: usize,
        header: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
        body: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
    ) -> Result<()>;

    fn prefix(&mut self, prefix: DiffPrefix);
    fn get_prefix(&self) -> DiffPrefix;

    fn inline_begin(&mut self) -> bool;
    fn inline_end(&mut self);
}

pub trait ValuePrinter: Write {
    fn link(
        &mut self,
        id: usize,
        f: &mut dyn FnMut(&mut dyn ValuePrinter) -> Result<()>,
    ) -> Result<()>;
}

pub(crate) struct PrintState<'a> {
    // 'w lifetime needed due to invariance
    printer: &'a mut dyn Printer,

    // The remaining fields contain information that is commonly needed in print methods.
    hash: &'a FileHash<'a>,
    code: Option<&'a Code<'a>>,
    options: &'a Options,
}

impl<'a> PrintState<'a> {
    #[inline]
    pub fn hash(&self) -> &'a FileHash<'a> {
        self.hash
    }

    #[inline]
    pub fn options(&self) -> &'a Options {
        self.options
    }

    pub fn new(
        printer: &'a mut dyn Printer,
        hash: &'a FileHash<'a>,
        code: Option<&'a Code<'a>>,
        options: &'a Options,
    ) -> Self {
        PrintState {
            printer,
            hash,
            code,
            options,
        }
    }

    // Output the header with an indented body.
    // If optional is true, then only output if the body is not empty.
    fn indent_impl<FHeader, FBody>(
        &mut self,
        optional: bool,
        collapsed: bool,
        mut header: FHeader,
        mut body: FBody,
    ) -> Result<()>
    where
        FHeader: FnMut(&mut PrintState) -> Result<()>,
        FBody: FnMut(&mut PrintState) -> Result<()>,
    {
        let hash = self.hash;
        let code = self.code;
        let options = self.options;
        let mut body_buf = Vec::new();
        self.printer.indent_body(&mut body_buf, &mut |printer| {
            let mut state = PrintState::new(printer, hash, code, options);
            body(&mut state)?;
            Ok(())
        })?;
        if !body_buf.is_empty() {
            self.printer
                .indent_header(collapsed, &*body_buf, &mut |printer| {
                    let mut state = PrintState::new(printer, hash, code, options);
                    header(&mut state)?;
                    Ok(())
                })?;
        } else if !optional {
            header(self)?;
        }
        Ok(())
    }

    pub fn collapsed<FHeader, FBody>(&mut self, header: FHeader, body: FBody) -> Result<()>
    where
        FHeader: FnMut(&mut PrintState) -> Result<()>,
        FBody: FnMut(&mut PrintState) -> Result<()>,
    {
        self.indent_impl(false, true, header, body)
    }

    pub fn id<FHeader, FBody>(
        &mut self,
        id: usize,
        mut header: FHeader,
        mut body: FBody,
    ) -> Result<()>
    where
        FHeader: FnMut(&mut PrintState) -> Result<()>,
        FBody: FnMut(&mut PrintState) -> Result<()>,
    {
        let hash = self.hash;
        let code = self.code;
        let options = self.options;
        self.printer.indent_id(
            id,
            &mut |printer| {
                let mut state = PrintState::new(printer, hash, code, options);
                header(&mut state)?;
                Ok(())
            },
            &mut |printer| {
                let mut state = PrintState::new(printer, hash, code, options);
                body(&mut state)?;
                Ok(())
            },
        )
    }

    pub fn expanded<FHeader, FBody>(&mut self, header: FHeader, body: FBody) -> Result<()>
    where
        FHeader: FnMut(&mut PrintState) -> Result<()>,
        FBody: FnMut(&mut PrintState) -> Result<()>,
    {
        self.indent_impl(false, false, header, body)
    }

    pub fn field_collapsed<FBody>(&mut self, label: &str, body: FBody) -> Result<()>
    where
        FBody: FnMut(&mut PrintState) -> Result<()>,
    {
        self.indent_impl(true, true, |state| state.label(label), body)
    }

    pub fn field_expanded<FBody>(&mut self, label: &str, body: FBody) -> Result<()>
    where
        FBody: FnMut(&mut PrintState) -> Result<()>,
    {
        self.indent_impl(true, false, |state| state.label(label), body)
    }

    pub fn inline<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState) -> Result<()>,
    {
        if self.printer.inline_begin() {
            let ret = f(self);
            self.printer.inline_end();
            ret
        } else {
            Ok(())
        }
    }

    fn prefix(
        &mut self,
        prefix: DiffPrefix,
        f: &mut dyn FnMut(&mut PrintState) -> Result<()>,
    ) -> Result<()> {
        self.printer.prefix(prefix);
        f(self)
    }

    pub fn line_break(&mut self) -> Result<()> {
        self.printer.line_break()
    }

    pub fn label(&mut self, label: &str) -> Result<()> {
        self.printer.line(label, &[])
    }

    fn line_impl<F>(&mut self, label: &str, mut f: F) -> Result<()>
    where
        F: FnMut(&mut dyn ValuePrinter, &FileHash) -> Result<()>,
    {
        let mut buf = Vec::new();
        let hash = self.hash;
        self.printer
            .value(&mut buf, &mut |printer| f(printer, hash))?;
        if !buf.is_empty() {
            self.printer.line(label, &*buf)?;
        }
        Ok(())
    }

    pub fn line<F>(&mut self, f: F) -> Result<()>
    where
        F: FnMut(&mut dyn ValuePrinter, &FileHash) -> Result<()>,
    {
        self.line_impl("", f)
    }

    pub fn field<F>(&mut self, label: &str, f: F) -> Result<()>
    where
        F: FnMut(&mut dyn ValuePrinter, &FileHash) -> Result<()>,
    {
        self.line_impl(label, f)
    }

    pub fn field_u64(&mut self, label: &str, arg: u64) -> Result<()> {
        self.field(label, |w, _| {
            write!(w, "{}", arg)?;
            Ok(())
        })
    }

    pub fn list<T: Print>(&mut self, arg: &T::Arg, list: &[T]) -> Result<()> {
        for item in list {
            item.print(self, arg)?;
        }
        Ok(())
    }

    pub fn sort_list<T: SortList>(&mut self, arg: &T::Arg, list: &mut [&T]) -> Result<()> {
        list.sort_by(|a, b| T::cmp_by(self.hash, a, self.hash, b, self.options));
        for item in list {
            item.print(self, arg)?;
        }
        Ok(())
    }
}

pub(crate) struct DiffState<'a> {
    printer: &'a mut dyn Printer,

    // True if DiffPrefix::Delete or DiffPrefix::Add was printed.
    diff: bool,

    // The remaining fields contain information that is commonly needed in print methods.
    hash_a: &'a FileHash<'a>,
    hash_b: &'a FileHash<'a>,
    code_a: Option<&'a Code<'a>>,
    code_b: Option<&'a Code<'a>>,
    options: &'a Options,
}

impl<'a> DiffState<'a> {
    #[inline]
    fn a(&mut self) -> PrintState {
        PrintState::new(self.printer, self.hash_a, self.code_a, self.options)
    }

    #[inline]
    fn b(&mut self) -> PrintState {
        PrintState::new(self.printer, self.hash_b, self.code_b, self.options)
    }

    #[inline]
    pub fn hash_a(&self) -> &'a FileHash<'a> {
        self.hash_a
    }

    #[inline]
    pub fn hash_b(&self) -> &'a FileHash<'a> {
        self.hash_b
    }

    #[inline]
    pub fn options(&self) -> &'a Options {
        self.options
    }

    pub fn new(
        printer: &'a mut dyn Printer,
        hash_a: &'a FileHash<'a>,
        hash_b: &'a FileHash<'a>,
        code_a: Option<&'a Code<'a>>,
        code_b: Option<&'a Code<'a>>,
        options: &'a Options,
    ) -> Self {
        DiffState {
            printer,
            diff: false,
            hash_a,
            hash_b,
            code_a,
            code_b,
            options,
        }
    }

    // Write output of `f` to a temporary buffer, then only
    // output that buffer if there were any differences.
    fn print_if_diff<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut DiffState) -> Result<()>,
    {
        let hash_a = self.hash_a;
        let hash_b = self.hash_b;
        let code_a = self.code_a;
        let code_b = self.code_b;
        let options = self.options;
        let mut buf = Vec::new();
        let mut diff = false;
        self.printer.buffer(&mut buf, &mut |printer| {
            let mut state = DiffState::new(printer, hash_a, hash_b, code_a, code_b, options);
            f(&mut state)?;
            diff = state.diff;
            Ok(())
        })?;
        if diff {
            self.diff = true;
        }
        if diff || options.html {
            self.printer.write_buf(&*buf)?;
        }
        Ok(())
    }

    // Don't allow `f` to update self.diff if flag is true.
    pub fn ignore_diff<F>(&mut self, flag: bool, mut f: F) -> Result<()>
    where
        F: FnMut(&mut DiffState) -> Result<()>,
    {
        let diff = self.diff;
        f(self)?;
        if flag {
            self.diff = diff;
        }
        Ok(())
    }

    // Output the header with an indented body.
    // If optional is true, then only output if the body is not empty.
    fn indent_impl<FHeader, FBody>(
        &mut self,
        optional: bool,
        collapsed: bool,
        mut header: FHeader,
        mut body: FBody,
    ) -> Result<()>
    where
        FHeader: FnMut(&mut DiffState) -> Result<()>,
        FBody: FnMut(&mut DiffState) -> Result<()>,
    {
        let hash_a = self.hash_a;
        let hash_b = self.hash_b;
        let code_a = self.code_a;
        let code_b = self.code_b;
        let options = self.options;

        let mut body_buf = Vec::new();
        let mut diff = false;
        self.printer.indent_body(&mut body_buf, &mut |printer| {
            printer.prefix(DiffPrefix::Equal);
            let mut state = DiffState::new(printer, hash_a, hash_b, code_a, code_b, options);
            body(&mut state)?;
            if state.diff {
                diff = true;
            }
            Ok(())
        })?;

        if !body_buf.is_empty() {
            self.printer
                .indent_header(collapsed, &*body_buf, &mut |printer| {
                    if diff {
                        printer.prefix(DiffPrefix::Modify);
                    } else {
                        printer.prefix(DiffPrefix::Equal);
                    }
                    let mut state =
                        DiffState::new(printer, hash_a, hash_b, code_a, code_b, options);
                    header(&mut state)?;
                    if state.diff {
                        diff = true;
                    }
                    Ok(())
                })?;
            if diff {
                self.diff = diff;
            }
        } else if !optional {
            header(self)?;
        }
        Ok(())
    }

    pub fn collapsed<FHeader, FBody>(&mut self, header: FHeader, body: FBody) -> Result<()>
    where
        FHeader: FnMut(&mut DiffState) -> Result<()>,
        FBody: FnMut(&mut DiffState) -> Result<()>,
    {
        self.indent_impl(false, true, header, body)
    }

    pub fn expanded<FHeader, FBody>(&mut self, header: FHeader, body: FBody) -> Result<()>
    where
        FHeader: FnMut(&mut DiffState) -> Result<()>,
        FBody: FnMut(&mut DiffState) -> Result<()>,
    {
        self.indent_impl(false, false, header, body)
    }

    pub fn field_collapsed<FBody>(&mut self, label: &str, body: FBody) -> Result<()>
    where
        FBody: FnMut(&mut DiffState) -> Result<()>,
    {
        self.indent_impl(true, true, |state| state.label(label), body)
    }

    pub fn field_expanded<FBody>(&mut self, label: &str, body: FBody) -> Result<()>
    where
        FBody: FnMut(&mut DiffState) -> Result<()>,
    {
        self.indent_impl(true, false, |state| state.label(label), body)
    }

    pub fn inline<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut DiffState) -> Result<()>,
    {
        if self.printer.inline_begin() {
            let ret = f(self);
            self.printer.inline_end();
            ret
        } else {
            Ok(())
        }
    }

    fn prefix_delete<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState) -> Result<()>,
    {
        self.a().prefix(DiffPrefix::Delete, &mut f)?;
        // Assume something is always written.
        self.diff = true;
        Ok(())
    }

    fn prefix_add<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState) -> Result<()>,
    {
        self.b().prefix(DiffPrefix::Add, &mut f)?;
        // Assume something is always written.
        self.diff = true;
        Ok(())
    }

    // Multiline blocks that are always different, but may be empty.
    pub fn block<F, T>(&mut self, arg_a: T, arg_b: T, mut f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState, T) -> Result<()>,
        T: Copy,
    {
        let hash_a = self.hash_a;
        let hash_b = self.hash_b;
        let code_a = self.code_a;
        let code_b = self.code_b;
        let options = self.options;
        let mut buf = Vec::new();
        self.printer.buffer(&mut buf, &mut |printer| {
            let mut state = DiffState::new(printer, hash_a, hash_b, code_a, code_b, options);
            state
                .a()
                .prefix(DiffPrefix::Delete, &mut |state| f(state, arg_a))?;
            state
                .b()
                .prefix(DiffPrefix::Add, &mut |state| f(state, arg_b))?;
            Ok(())
        })?;
        if !buf.is_empty() {
            self.printer.write_buf(&*buf)?;
            self.diff = true;
        }
        Ok(())
    }

    pub fn line_break(&mut self) -> Result<()> {
        self.printer.line_break()
    }

    pub fn label(&mut self, label: &str) -> Result<()> {
        if self.printer.get_prefix() != DiffPrefix::Modify {
            self.printer.prefix(DiffPrefix::Equal);
        }
        self.printer.line(label, &[])
    }

    fn line_impl<F, T>(
        &mut self,
        id: usize,
        label: &str,
        arg_a: T,
        arg_b: T,
        mut f: F,
    ) -> Result<()>
    where
        F: FnMut(&mut dyn ValuePrinter, &FileHash, T) -> Result<()>,
        T: Copy,
    {
        let mut a = Vec::new();
        let hash_a = self.hash_a;
        self.printer
            .value(&mut a, &mut |printer| f(printer, hash_a, arg_a))?;

        let mut b = Vec::new();
        let hash_b = self.hash_b;
        self.printer
            .value(&mut b, &mut |printer| f(printer, hash_b, arg_b))?;

        if a == b {
            if !a.is_empty() {
                if self.printer.get_prefix() != DiffPrefix::Modify {
                    self.printer.prefix(DiffPrefix::Equal);
                }
                self.printer.line(label, &*a)?;
            }
        } else {
            if a.is_empty() {
                self.printer.prefix(DiffPrefix::Add);
                self.printer.line(label, &*b)?;
            } else if b.is_empty() {
                self.printer.prefix(DiffPrefix::Delete);
                self.printer.line(label, &*a)?;
            } else {
                self.printer.line_diff(id, label, &*a, &*b)?;
            }
            self.diff = true;
        }
        Ok(())
    }

    pub fn line<F, T>(&mut self, arg_a: T, arg_b: T, f: F) -> Result<()>
    where
        F: FnMut(&mut dyn ValuePrinter, &FileHash, T) -> Result<()>,
        T: Copy,
    {
        self.line_impl(0, "", arg_a, arg_b, f)
    }

    pub fn id<F, T>(&mut self, id: usize, arg_a: T, arg_b: T, f: F) -> Result<()>
    where
        F: FnMut(&mut dyn ValuePrinter, &FileHash, T) -> Result<()>,
        T: Copy,
    {
        self.line_impl(id, "", arg_a, arg_b, f)
    }

    pub fn field<F, T>(&mut self, label: &str, arg_a: T, arg_b: T, f: F) -> Result<()>
    where
        F: FnMut(&mut dyn ValuePrinter, &FileHash, T) -> Result<()>,
        T: Copy,
    {
        self.line_impl(0, label, arg_a, arg_b, f)
    }

    pub fn field_u64(&mut self, label: &str, arg_a: u64, arg_b: u64) -> Result<()> {
        let base = arg_a;
        self.field(label, arg_a, arg_b, |w, _hash, arg| {
            write!(w, "{}", arg)?;
            if arg != base {
                write!(w, " ({:+})", arg as i64 - base as i64)?;
            }
            Ok(())
        })
    }

    pub fn list<T: DiffList>(
        &mut self,
        arg_a: &T::Arg,
        list_a: &[T],
        arg_b: &T::Arg,
        list_b: &[T],
    ) -> Result<()> {
        let path = shortest_path(
            list_a,
            list_b,
            |a| a.step_cost(self, arg_a),
            |b| b.step_cost(self, arg_b),
            |a, b| T::diff_cost(self, arg_a, a, arg_b, b),
        );
        let mut iter_a = list_a.iter();
        let mut iter_b = list_b.iter();
        for dir in path {
            match dir {
                Direction::None => break,
                Direction::Diagonal => {
                    if let (Some(a), Some(b)) = (iter_a.next(), iter_b.next()) {
                        T::diff(self, arg_a, a, arg_b, b)?;
                    }
                }
                Direction::Horizontal => {
                    if let Some(a) = iter_a.next() {
                        self.prefix_delete(|state| a.print(state, arg_a))?;
                    }
                }
                Direction::Vertical => {
                    if let Some(b) = iter_b.next() {
                        self.prefix_add(|state| b.print(state, arg_b))?;
                    }
                }
            }
        }
        Ok(())
    }

    // This is similar to `list`, but because the items are ordered
    // we can do a greedy search.
    //
    // The caller must provide lists that are already sorted.
    pub fn ord_list<T: Ord + Print>(
        &mut self,
        arg_a: &T::Arg,
        list_a: &[T],
        arg_b: &T::Arg,
        list_b: &[T],
    ) -> Result<()> {
        for item in MergeIterator::new(list_a.iter(), list_b.iter(), <&T>::cmp) {
            match item {
                MergeResult::Both(a, b) => {
                    T::diff(self, arg_a, a, arg_b, b)?;
                }
                MergeResult::Left(a) => {
                    self.prefix_delete(|state| a.print(state, arg_a))?;
                }
                MergeResult::Right(b) => {
                    self.prefix_add(|state| b.print(state, arg_b))?;
                }
            }
        }
        Ok(())
    }

    // Sort then display a merged list of items.
    //
    // Items with no difference are not displayed.
    //
    // Also, self.options controls:
    // - sort order
    // - display of added/deleted options
    pub fn sort_list<'i, T: SortList>(
        &mut self,
        arg_a: &T::Arg,
        arg_b: &T::Arg,
        list: &mut [MergeResult<&'i T, &'i T>],
    ) -> Result<()>
    where
        T: 'i,
    {
        list.sort_by(|x, y| {
            MergeResult::cmp(x, y, &self.hash_a, &self.hash_b, |x, hash_x, y, hash_y| {
                T::cmp_by(hash_x, x, hash_y, y, self.options)
            })
        });

        for item in list {
            match *item {
                MergeResult::Both(a, b) => {
                    self.print_if_diff(|state| T::diff(state, arg_a, a, arg_b, b))?;
                }
                MergeResult::Left(a) => {
                    if !self.options.ignore_deleted {
                        self.prefix_delete(|state| a.print(state, arg_a))?;
                    }
                }
                MergeResult::Right(b) => {
                    if !self.options.ignore_added {
                        self.prefix_add(|state| b.print(state, arg_b))?;
                    }
                }
            }
        }
        Ok(())
    }
}

pub(crate) trait Print {
    type Arg;

    // TODO: need associated type constructor to avoid requiring arg to be a reference?
    fn print(&self, state: &mut PrintState, arg: &Self::Arg) -> Result<()>;

    fn diff(
        state: &mut DiffState,
        arg_a: &Self::Arg,
        a: &Self,
        arg_b: &Self::Arg,
        b: &Self,
    ) -> Result<()>;
}

impl<'a, T> Print for &'a T
where
    T: Print,
{
    type Arg = T::Arg;

    fn print(&self, state: &mut PrintState, arg: &Self::Arg) -> Result<()> {
        T::print(*self, state, arg)
    }

    fn diff(
        state: &mut DiffState,
        arg_a: &Self::Arg,
        a: &Self,
        arg_b: &Self::Arg,
        b: &Self,
    ) -> Result<()> {
        T::diff(state, arg_a, *a, arg_b, *b)
    }
}

pub(crate) trait PrintHeader {
    fn print_header(&self, state: &mut PrintState) -> Result<()>;
    fn print_body(&self, state: &mut PrintState, unit: &parser::Unit) -> Result<()>;
}

pub(crate) trait DiffList: Print {
    fn step_cost(&self, state: &DiffState, arg: &Self::Arg) -> usize;

    fn diff_cost(
        state: &DiffState,
        arg_a: &Self::Arg,
        a: &Self,
        arg_b: &Self::Arg,
        b: &Self,
    ) -> usize;
}

pub(crate) trait SortList: Print {
    fn cmp_id(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering;

    fn cmp_id_for_sort(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering {
        Self::cmp_id(hash_a, a, hash_b, b, options)
    }

    fn cmp_by(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering;
}

pub enum MergeResult<T, U> {
    Left(T),
    Right(U),
    Both(T, U),
}

impl<T> MergeResult<T, T> {
    fn cmp<Arg, F>(x: &Self, y: &Self, arg_left: Arg, arg_right: Arg, f: F) -> cmp::Ordering
    where
        Arg: Copy,
        F: Fn(&T, Arg, &T, Arg) -> cmp::Ordering,
    {
        match *x {
            MergeResult::Both(_, ref x_right) => match *y {
                MergeResult::Both(_, ref y_right) => f(x_right, arg_right, y_right, arg_right),
                MergeResult::Left(ref y_left) => f(x_right, arg_right, y_left, arg_left),
                MergeResult::Right(ref y_right) => f(x_right, arg_right, y_right, arg_right),
            },
            MergeResult::Left(ref x_left) => match *y {
                MergeResult::Both(_, ref y_right) => f(x_left, arg_left, y_right, arg_right),
                MergeResult::Left(ref y_left) => f(x_left, arg_left, y_left, arg_left),
                MergeResult::Right(ref y_right) => f(x_left, arg_left, y_right, arg_right),
            },
            MergeResult::Right(ref x_right) => match *y {
                MergeResult::Both(_, ref y_right) => f(x_right, arg_right, y_right, arg_right),
                MergeResult::Left(ref y_left) => f(x_right, arg_right, y_left, arg_left),
                MergeResult::Right(ref y_right) => f(x_right, arg_right, y_right, arg_right),
            },
        }
    }
}

pub struct MergeIterator<T, U, L, R, C>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = U>,
    C: Fn(&T, &U) -> cmp::Ordering,
{
    iter_left: L,
    iter_right: R,
    item_left: Option<T>,
    item_right: Option<U>,
    item_cmp: C,
}

impl<T, U, L, R, C> MergeIterator<T, U, L, R, C>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = U>,
    C: Fn(&T, &U) -> cmp::Ordering,
{
    pub fn new(mut iter_left: L, mut iter_right: R, item_cmp: C) -> Self {
        let item_left = iter_left.next();
        let item_right = iter_right.next();
        MergeIterator {
            iter_left,
            iter_right,
            item_left,
            item_right,
            item_cmp,
        }
    }
}

impl<T, U, L, R, C> Iterator for MergeIterator<T, U, L, R, C>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = U>,
    C: Fn(&T, &U) -> cmp::Ordering,
{
    type Item = MergeResult<T, U>;

    fn next(&mut self) -> Option<MergeResult<T, U>> {
        match (self.item_left.take(), self.item_right.take()) {
            (Some(left), Some(right)) => match (self.item_cmp)(&left, &right) {
                cmp::Ordering::Equal => {
                    self.item_left = self.iter_left.next();
                    self.item_right = self.iter_right.next();
                    Some(MergeResult::Both(left, right))
                }
                cmp::Ordering::Less => {
                    self.item_left = self.iter_left.next();
                    self.item_right = Some(right);
                    Some(MergeResult::Left(left))
                }
                cmp::Ordering::Greater => {
                    self.item_left = Some(left);
                    self.item_right = self.iter_right.next();
                    Some(MergeResult::Right(right))
                }
            },
            (Some(left), None) => {
                self.item_left = self.iter_left.next();
                Some(MergeResult::Left(left))
            }
            (None, Some(right)) => {
                self.item_right = self.iter_right.next();
                Some(MergeResult::Right(right))
            }
            (None, None) => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Direction {
    None,
    Diagonal,
    Horizontal,
    Vertical,
}

#[derive(Debug, Clone, Copy)]
struct Node {
    cost: usize,
    from: Direction,
    done: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct State {
    cost: usize,
    index1: usize,
    index2: usize,
}

impl Ord for State {
    fn cmp(&self, other: &State) -> cmp::Ordering {
        // min-heap
        other.cost.cmp(&self.cost)
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &State) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// Use Dijkstra's algorithm to find the shortest edit path between two arrays.
//
// step_cost is used for add/delete operations.
//
// diff_cost is used to calculate the cost for modify operations. It should
// return:
//     0 for items that are completely equal
//     (2 * step_cost) for items that are completely different
//     values in between for items that are partially equal
fn shortest_path<Item, Step1, Step2, Diff>(
    item1: &[Item],
    item2: &[Item],
    step_cost1: Step1,
    step_cost2: Step2,
    diff_cost: Diff,
) -> Vec<Direction>
where
    Step1: Fn(&Item) -> usize,
    Step2: Fn(&Item) -> usize,
    Diff: Fn(&Item, &Item) -> usize,
{
    // len + 1 because we need to allow for the 0 items state too.
    let len1 = item1.len() + 1;
    let len2 = item2.len() + 1;
    let len = len1 * len2;

    let mut node: Vec<Node> = vec![
        Node {
            cost: usize::MAX,
            from: Direction::None,
            done: false,
        };
        len
    ];
    let mut heap = BinaryHeap::new();

    fn push(
        node: &mut Node,
        heap: &mut BinaryHeap<State>,
        index1: usize,
        index2: usize,
        cost: usize,
        from: Direction,
    ) {
        if cost < node.cost {
            node.cost = cost;
            node.from = from;
            heap.push(State {
                cost,
                index1,
                index2,
            });
        }
    }

    // Start at the end.  This makes indexing and boundary conditions
    // simpler, and also means we can backtrack in order.
    push(
        &mut node[len - 1],
        &mut heap,
        len1 - 1,
        len2 - 1,
        0,
        Direction::None,
    );

    while let Some(State { index1, index2, .. }) = heap.pop() {
        if (index1, index2) == (0, 0) {
            let mut result = Vec::new();
            let mut index1 = 0;
            let mut index2 = 0;
            loop {
                let index = index1 + index2 * len1;
                let from = node[index].from;
                match from {
                    Direction::None => {
                        return result;
                    }
                    Direction::Diagonal => {
                        index1 += 1;
                        index2 += 1;
                    }
                    Direction::Horizontal => {
                        index1 += 1;
                    }
                    Direction::Vertical => {
                        index2 += 1;
                    }
                }
                result.push(from);
            }
        }

        let index = index1 + index2 * len1;
        if node[index].done {
            continue;
        }
        node[index].done = true;

        if index2 > 0 {
            let next2 = index2 - 1;
            let next = index - len1;
            if !node[next].done {
                let cost = node[index].cost + step_cost2(&item2[next2]);
                push(
                    &mut node[next],
                    &mut heap,
                    index1,
                    next2,
                    cost,
                    Direction::Vertical,
                );
            }
        }
        if index1 > 0 {
            let next1 = index1 - 1;
            let next = index - 1;
            if !node[next].done {
                let cost = node[index].cost + step_cost1(&item1[next1]);
                push(
                    &mut node[next],
                    &mut heap,
                    next1,
                    index2,
                    cost,
                    Direction::Horizontal,
                );
            }
        }
        if index1 > 0 && index2 > 0 {
            let next1 = index1 - 1;
            let next2 = index2 - 1;
            let next = index - len1 - 1;
            if !node[next].done {
                let step_cost = step_cost1(&item1[next1]) + step_cost2(&item2[next2]);
                let diff_cost = diff_cost(&item1[next1], &item2[next2]);
                if diff_cost < step_cost {
                    let cost = node[index].cost + diff_cost;
                    push(
                        &mut node[next],
                        &mut heap,
                        next1,
                        next2,
                        cost,
                        Direction::Diagonal,
                    );
                }
            }
        }
    }

    panic!("failed to find shortest path");
}
