use std::io::Write;
use std::cmp;

use {File, FileHash, Options, Result, Unit};
use diff;

#[derive(Debug, Clone, Copy)]
enum DiffPrefix {
    None,
    Equal,
    Less,
    Greater,
}

pub(crate) struct PrintState<'a, 'input>
where
    'input: 'a,
{
    indent: usize,
    prefix: DiffPrefix,
    // True if DiffPrefix::Less or DiffPrefix::Greater was printed.
    diff: bool,
    inline_depth: usize,

    // The remaining fields contain information that is commonly needed in print methods.
    pub file: &'a File<'input>,
    pub hash: &'a FileHash<'a, 'input>,
    pub options: &'a Options<'a>,
}

impl<'a, 'input> PrintState<'a, 'input>
where
    'input: 'a,
{
    pub fn new(
        file: &'a File<'input>,
        hash: &'a FileHash<'a, 'input>,
        options: &'a Options<'a>,
    ) -> Self {
        PrintState {
            indent: 0,
            prefix: DiffPrefix::None,
            diff: false,
            inline_depth: options.inline_depth,
            file: file,
            hash: hash,
            options: options,
        }
    }

    pub fn indent<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>,
    {
        self.indent += 1;
        let ret = f(self);
        self.indent -= 1;
        ret
    }

    pub fn inline<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>,
    {
        if self.inline_depth == 0 {
            return Ok(());
        }
        self.inline_depth -= 1;
        let ret = f(self);
        self.inline_depth += 1;
        ret
    }


    fn prefix<F>(&mut self, prefix: DiffPrefix, mut f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>,
    {
        let prev = self.prefix;
        self.prefix = prefix;
        let ret = f(self);
        self.prefix = prev;
        ret
    }

    pub fn line<F>(&mut self, w: &mut Write, mut f: F) -> Result<()>
    where
        F: FnMut(&mut Write, &mut PrintState<'a, 'input>) -> Result<()>,
    {
        match self.prefix {
            DiffPrefix::None => {}
            DiffPrefix::Equal => write!(w, "  ")?,
            DiffPrefix::Less => {
                write!(w, "- ")?;
                self.diff = true;
            }
            DiffPrefix::Greater => {
                write!(w, "+ ")?;
                self.diff = true;
            }
        }
        for _ in 0..self.indent {
            write!(w, "\t")?;
        }
        f(w, self)?;
        write!(w, "\n")?;
        Ok(())
    }

    pub fn line_option<F>(&mut self, w: &mut Write, mut f: F) -> Result<()>
    where
        F: FnMut(&mut Write, &mut PrintState<'a, 'input>) -> Result<()>,
    {
        let mut buf = Vec::new();
        let mut state = PrintState::new(self.file, self.hash, self.options);
        f(&mut buf, &mut state)?;
        if !buf.is_empty() {
            self.line(w, |w, _state| w.write_all(&*buf).map_err(From::from))?;
        }
        Ok(())
    }

    pub fn list<T: PrintList>(
        &mut self,
        label: &str,
        w: &mut Write,
        unit: &Unit,
        list: &[T],
    ) -> Result<()> {
        if list.is_empty() {
            return Ok(());
        }

        if !label.is_empty() {
            self.line(w, |w, _state| {
                write!(w, "{}:", label)?;
                Ok(())
            })?;
        }

        self.indent(|state| {
            for item in list {
                item.print_list(w, state, unit)?;
            }
            Ok(())
        })
    }
}

pub(crate) struct DiffState<'a, 'input>
where
    'input: 'a,
{
    pub a: PrintState<'a, 'input>,
    pub b: PrintState<'a, 'input>,
    pub options: &'a Options<'a>,
}

impl<'a, 'input> DiffState<'a, 'input>
where
    'input: 'a,
{
    pub fn new(
        file_a: &'a File<'input>,
        hash_a: &'a FileHash<'a, 'input>,
        file_b: &'a File<'input>,
        hash_b: &'a FileHash<'a, 'input>,
        options: &'a Options<'a>,
    ) -> Self {
        DiffState {
            a: PrintState::new(file_a, hash_a, options),
            b: PrintState::new(file_b, hash_b, options),
            options: options,
        }
    }

    // This is similar to `list`, but because the items are ordered
    // we can do a greedy search.
    pub fn merge<T, I, FIterA, FIterB, FCmp, FEqual, FLess, FGreater>(
        &mut self,
        w: &mut Write,
        iter_a: FIterA,
        iter_b: FIterB,
        cmp: FCmp,
        mut equal: FEqual,
        less: FLess,
        greater: FGreater,
    ) -> Result<()>
    where
        T: Copy,
        I: IntoIterator<Item = T>,
        FIterA: Fn(&PrintState<'a, 'input>) -> I,
        FIterB: Fn(&PrintState<'a, 'input>) -> I,
        FCmp: Fn(&FileHash, T, &FileHash, T) -> cmp::Ordering,
        FEqual: FnMut(&mut Write, &mut DiffState<'a, 'input>, T, T) -> Result<()>,
        FLess: Fn(&mut Write, &mut PrintState<'a, 'input>, T) -> Result<()>,
        FGreater: Fn(&mut Write, &mut PrintState<'a, 'input>, T) -> Result<()>,
    {
        let iter_a = &mut iter_a(&self.a).into_iter();
        let iter_b = &mut iter_b(&self.b).into_iter();
        let hash_a = self.a.hash;
        let hash_b = self.b.hash;
        for m in MergeIterator::new(iter_a, iter_b, |a, b| cmp(hash_a, a, hash_b, b)) {
            match m {
                MergeResult::Both(l, r) => self.prefix_equal(|state| equal(w, state, l, r))?,
                MergeResult::Left(l) => self.prefix_less(|state| less(w, state, l))?,
                MergeResult::Right(r) => self.prefix_greater(|state| greater(w, state, r))?,
            }
        }
        Ok(())
    }

    pub fn diff<F>(&mut self, w: &mut Write, mut f: F) -> Result<()>
    where
        F: FnMut(&mut Write, &mut DiffState<'a, 'input>) -> Result<()>,
    {
        let mut buf = Vec::new();
        self.a.diff = false;
        self.b.diff = false;
        f(&mut buf, self)?;
        if self.a.diff || self.b.diff {
            w.write_all(&*buf)?;
        }
        Ok(())
    }

    pub fn ignore_diff<F>(&mut self, flag: bool, mut f: F) -> Result<()>
    where
        F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>,
    {
        let a_diff = self.a.diff;
        let b_diff = self.b.diff;
        f(self)?;
        if flag {
            self.a.diff = a_diff;
            self.b.diff = b_diff;
        }
        Ok(())
    }

    pub fn indent<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>,
    {
        self.a.indent += 1;
        self.b.indent += 1;
        let ret = f(self);
        self.a.indent -= 1;
        self.b.indent -= 1;
        ret
    }

    pub fn inline<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>,
    {
        if self.a.inline_depth == 0 {
            return Ok(());
        }
        self.a.inline_depth -= 1;
        self.b.inline_depth -= 1;
        let ret = f(self);
        self.a.inline_depth += 1;
        self.b.inline_depth += 1;
        ret
    }

    fn prefix_equal<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>,
    {
        let prev_a = self.a.prefix;
        let prev_b = self.b.prefix;
        self.a.prefix = DiffPrefix::Equal;
        self.b.prefix = DiffPrefix::Equal;
        let ret = f(self);
        self.a.prefix = prev_a;
        self.b.prefix = prev_b;
        ret
    }

    fn prefix_less<F>(&mut self, f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>,
    {
        self.a.prefix(DiffPrefix::Less, f)
    }

    fn prefix_greater<F>(&mut self, f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>,
    {
        self.b.prefix(DiffPrefix::Greater, f)
    }

    pub fn prefix_diff<F>(&mut self, mut f: F) -> Result<()>
    where
        F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>,
    {
        let prev_a = self.a.prefix;
        let prev_b = self.b.prefix;
        self.a.prefix = DiffPrefix::Less;
        self.b.prefix = DiffPrefix::Greater;
        let ret = f(self);
        self.a.prefix = prev_a;
        self.b.prefix = prev_b;
        ret
    }

    pub fn line<F, T>(&mut self, w: &mut Write, arg_a: T, arg_b: T, mut f: F) -> Result<()>
    where
        F: FnMut(&mut Write, &mut PrintState<'a, 'input>, T) -> Result<()>,
    {
        let mut a = Vec::new();
        let mut state = PrintState::new(self.a.file, self.a.hash, self.a.options);
        f(&mut a, &mut state, arg_a)?;

        let mut b = Vec::new();
        let mut state = PrintState::new(self.b.file, self.b.hash, self.b.options);
        f(&mut b, &mut state, arg_b)?;

        if a == b {
            self.prefix_equal(|state| {
                if !a.is_empty() {
                    state.a.line(w, |w, _state| w.write_all(&*a).map_err(From::from))?;
                }
                Ok(())
            })
        } else {
            self.prefix_diff(|state| {
                if !a.is_empty() {
                    state.a.line(w, |w, _state| w.write_all(&*a).map_err(From::from))?;
                }
                if !b.is_empty() {
                    state.b.line(w, |w, _state| w.write_all(&*b).map_err(From::from))?;
                }
                Ok(())
            })
        }
    }

    /// This is the same as `Self::line`. It exists for symmetry with `PrintState::line_option`.
    pub fn line_option<F, T>(&mut self, w: &mut Write, arg_a: T, arg_b: T, f: F) -> Result<()>
    where
        F: FnMut(&mut Write, &mut PrintState<'a, 'input>, T) -> Result<()>,
    {
        self.line(w, arg_a, arg_b, f)
    }

    pub fn line_option_u64(
        &mut self,
        w: &mut Write,
        label: &str,
        arg_a: Option<u64>,
        arg_b: Option<u64>,
    ) -> Result<()> {
        let base = arg_a.unwrap_or(0);
        self.line_option(w, arg_a, arg_b, |w, _state, arg| {
            if let Some(arg) = arg {
                write!(w, "{}: {}", label, arg)?;
                if arg != base {
                    write!(w, " ({:+})", arg as i64 - base as i64)?;
                }
            }
            Ok(())
        })
    }

    pub fn list<T: DiffList>(
        &mut self,
        label: &str,
        w: &mut Write,
        unit_a: &Unit,
        list_a: &[T],
        unit_b: &Unit,
        list_b: &[T],
    ) -> Result<()> {
        if list_a.is_empty() && list_b.is_empty() {
            return Ok(());
        }

        if !label.is_empty() {
            self.line(w, list_a, list_b, |w, _state, list| {
                if !list.is_empty() {
                    write!(w, "{}:", label)?;
                }
                Ok(())
            })?;
        }

        self.indent(|state| {
            let path = diff::shortest_path(
                list_a,
                list_b,
                T::step_cost(),
                |a, b| T::diff_cost(state, unit_a, a, unit_b, b),
            );
            let mut iter_a = list_a.iter();
            let mut iter_b = list_b.iter();
            for dir in path {
                match dir {
                    diff::Direction::None => break,
                    diff::Direction::Diagonal => {
                        if let (Some(a), Some(b)) = (iter_a.next(), iter_b.next()) {
                            T::diff_list(w, state, unit_a, a, unit_b, b)?;
                        }
                    }
                    diff::Direction::Horizontal => if let Some(a) = iter_a.next() {
                        state.prefix_less(|state| a.print_list(w, state, unit_a))?;
                    },
                    diff::Direction::Vertical => if let Some(b) = iter_b.next() {
                        state.prefix_greater(|state| b.print_list(w, state, unit_b))?;
                    },
                }
            }
            Ok(())
        })
    }
}

pub(crate) trait PrintList {
    fn print_list(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()>;
}

impl<'a, T> PrintList for &'a T
where
    T: PrintList,
{
    fn print_list(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        T::print_list(*self, w, state, unit)
    }
}

pub(crate) trait DiffList: PrintList {
    fn step_cost() -> usize;

    fn diff_cost(state: &DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> usize;

    fn diff_list(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Self,
        unit_b: &Unit,
        b: &Self,
    ) -> Result<()>;
}

enum MergeResult<T> {
    Left(T),
    Right(T),
    Both(T, T),
}

struct MergeIterator<T, I, C>
where
    T: Copy,
    I: Iterator<Item = T>,
    C: Fn(T, T) -> cmp::Ordering,
{
    iter_left: I,
    iter_right: I,
    item_left: Option<T>,
    item_right: Option<T>,
    item_cmp: C,
}

impl<T, I, C> MergeIterator<T, I, C>
where
    T: Copy,
    I: Iterator<Item = T>,
    C: Fn(T, T) -> cmp::Ordering,
{
    fn new(mut left: I, mut right: I, cmp: C) -> Self {
        let item_left = left.next();
        let item_right = right.next();
        MergeIterator {
            iter_left: left,
            iter_right: right,
            item_left: item_left,
            item_right: item_right,
            item_cmp: cmp,
        }
    }
}

impl<T, I, C> Iterator for MergeIterator<T, I, C>
where
    T: Copy,
    I: Iterator<Item = T>,
    C: Fn(T, T) -> cmp::Ordering,
{
    type Item = MergeResult<T>;

    fn next(&mut self) -> Option<MergeResult<T>> {
        match (self.item_left, self.item_right) {
            (Some(left), Some(right)) => match (self.item_cmp)(left, right) {
                cmp::Ordering::Equal => {
                    self.item_left = self.iter_left.next();
                    self.item_right = self.iter_right.next();
                    Some(MergeResult::Both(left, right))
                }
                cmp::Ordering::Less => {
                    self.item_left = self.iter_left.next();
                    Some(MergeResult::Left(left))
                }
                cmp::Ordering::Greater => {
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
