use std::cmp;
use std::collections::BinaryHeap;
use std::io::Write;
use std::usize;

use {Options, Result};
use file::FileHash;

#[derive(Debug, Clone, Copy)]
enum DiffPrefix {
    None,
    Equal,
    Less,
    Greater,
}

pub(crate) struct Printer<'w> {
    w: &'w mut Write,
    indent: usize,
    prefix: DiffPrefix,
    inline_depth: usize,
}

impl<'w> Printer<'w> {
    pub fn new(w: &'w mut Write, options: &Options) -> Self {
        Printer {
            w,
            indent: 0,
            prefix: DiffPrefix::None,
            inline_depth: options.inline_depth,
        }
    }

    pub fn temp<'temp>(&self, temp: &'temp mut Write) -> Printer<'temp> {
        Printer {
            w: temp,
            indent: self.indent,
            prefix: self.prefix,
            inline_depth: self.inline_depth,
        }
    }
}

pub(crate) struct PrintState<'a, 'w>
where
    'w: 'a,
{
    // 'w lifetime needed due to invariance
    printer: &'a mut Printer<'w>,

    // The remaining fields contain information that is commonly needed in print methods.
    hash: &'a FileHash<'a>,
    options: &'a Options<'a>,
}

impl<'a, 'w> PrintState<'a, 'w>
where
    'w: 'a,
{
    #[inline]
    pub fn w(&mut self) -> &mut Write {
        self.printer.w
    }

    #[inline]
    pub fn hash(&self) -> &'a FileHash<'a> {
        self.hash
    }

    #[inline]
    pub fn options(&self) -> &'a Options<'a> {
        self.options
    }

    pub fn new(
        printer: &'a mut Printer<'w>,
        hash: &'a FileHash<'a>,
        options: &'a Options<'a>,
    ) -> Self {
        PrintState {
            printer,
            hash: hash,
            options: options,
        }
    }

    pub fn indent<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut PrintState) -> Result<()>,
    {
        self.printer.indent += 1;
        let ret = f(self);
        self.printer.indent -= 1;
        ret
    }

    pub fn inline<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut PrintState) -> Result<()>,
    {
        if self.printer.inline_depth == 0 {
            return Ok(());
        }
        self.printer.inline_depth -= 1;
        let ret = f(self);
        self.printer.inline_depth += 1;
        ret
    }

    fn prefix<F>(&mut self, prefix: DiffPrefix, f: F) -> Result<()>
    where
        F: FnOnce(&mut PrintState) -> Result<()>,
    {
        self.printer.prefix = prefix;
        f(self)
    }

    pub fn line<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut Write, &FileHash) -> Result<()>,
    {
        match self.printer.prefix {
            DiffPrefix::None => {}
            DiffPrefix::Equal => write!(self.w(), "  ")?,
            DiffPrefix::Less => {
                write!(self.w(), "- ")?;
            }
            DiffPrefix::Greater => {
                write!(self.w(), "+ ")?;
            }
        }
        for _ in 0..self.printer.indent {
            write!(self.w(), "\t")?;
        }
        f(self.printer.w, self.hash)?;
        write!(self.w(), "\n")?;
        Ok(())
    }

    pub fn line_option<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut Write, &FileHash) -> Result<()>,
    {
        let mut buf = Vec::new();
        f(&mut buf, self.hash)?;
        if !buf.is_empty() {
            self.line(|w, _hash| w.write_all(&*buf).map_err(From::from))?;
        }
        Ok(())
    }

    pub fn line_u64(&mut self, label: &str, arg: u64) -> Result<()> {
        self.line(|w, _hash| {
            write!(w, "{}: {}", label, arg)?;
            Ok(())
        })
    }

    pub fn list<T: Print>(&mut self, label: &str, arg: &T::Arg, list: &[T]) -> Result<()> {
        if list.is_empty() {
            return Ok(());
        }

        if !label.is_empty() {
            self.line(|w, _hash| {
                write!(w, "{}:", label)?;
                Ok(())
            })?;
        }

        self.indent(|state| {
            for item in list {
                item.print(state, arg)?;
            }
            Ok(())
        })
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
    printer: &'a mut Printer<'a>,

    // True if DiffPrefix::Less or DiffPrefix::Greater was printed.
    diff: bool,

    // The remaining fields contain information that is commonly needed in print methods.
    hash_a: &'a FileHash<'a>,
    hash_b: &'a FileHash<'a>,
    options: &'a Options<'a>,
}

impl<'a> DiffState<'a> {
    #[inline]
    pub fn w(&mut self) -> &mut Write {
        self.printer.w
    }

    #[inline]
    fn a<'me>(&'me mut self) -> PrintState<'me, 'a> {
        PrintState::new(self.printer, self.hash_a, self.options)
    }

    #[inline]
    fn b<'me>(&'me mut self) -> PrintState<'me, 'a> {
        PrintState::new(self.printer, self.hash_b, self.options)
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
    pub fn options(&self) -> &'a Options<'a> {
        self.options
    }

    pub fn new(
        printer: &'a mut Printer<'a>,
        hash_a: &'a FileHash<'a>,
        hash_b: &'a FileHash<'a>,
        options: &'a Options<'a>,
    ) -> Self {
        DiffState {
            printer,
            diff: false,
            hash_a,
            hash_b,
            options: options,
        }
    }

    // Write output of `f` to a temporary buffer, then only
    // output that buffer if there were any differences.
    pub fn diff<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut DiffState) -> Result<()>,
    {
        let mut buf = Vec::new();
        let diff = {
            let mut printer = self.printer.temp(&mut buf);
            let mut state = DiffState::new(&mut printer, self.hash_a, self.hash_b, self.options);
            f(&mut state)?;
            state.diff
        };
        if diff {
            self.w().write_all(&*buf)?;
            self.diff = true;
        }
        Ok(())
    }

    // Don't allow `f` to update self.diff if flag is true.
    pub fn ignore_diff<F>(&mut self, flag: bool, f: F) -> Result<()>
    where
        F: FnOnce(&mut DiffState) -> Result<()>,
    {
        let diff = self.diff;
        f(self)?;
        if flag {
            self.diff = diff;
        }
        Ok(())
    }

    pub fn indent<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut DiffState) -> Result<()>,
    {
        self.printer.indent += 1;
        let ret = f(self);
        self.printer.indent -= 1;
        ret
    }

    pub fn inline<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut DiffState) -> Result<()>,
    {
        if self.printer.inline_depth == 0 {
            return Ok(());
        }
        self.printer.inline_depth -= 1;
        let ret = f(self);
        self.printer.inline_depth += 1;
        ret
    }

    fn prefix_equal<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut PrintState) -> Result<()>,
    {
        self.a().prefix(DiffPrefix::Equal, f)
    }

    fn prefix_less<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut PrintState) -> Result<()>,
    {
        self.a().prefix(DiffPrefix::Less, f)?;
        // Assume something is always written.
        self.diff = true;
        Ok(())
    }

    fn prefix_greater<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&mut PrintState) -> Result<()>,
    {
        self.b().prefix(DiffPrefix::Greater, f)?;
        // Assume something is always written.
        self.diff = true;
        Ok(())
    }

    // Multiline blocks that are always different, but may be empty.
    pub fn block<F, T>(&mut self, arg_a: T, arg_b: T, mut f: F) -> Result<()>
    where
        F: FnMut(&mut PrintState, T) -> Result<()>,
    {
        let mut buf = Vec::new();
        {
            let mut printer = self.printer.temp(&mut buf);
            let mut state = DiffState::new(&mut printer, self.hash_a, self.hash_b, self.options);
            state.a().prefix(DiffPrefix::Less, |state| f(state, arg_a))?;
            state.b().prefix(DiffPrefix::Greater, |state| f(state, arg_b))?;
        }
        if !buf.is_empty() {
            self.w().write_all(&*buf)?;
            self.diff = true;
        }
        Ok(())
    }

    pub fn line<F, T>(&mut self, arg_a: T, arg_b: T, mut f: F) -> Result<()>
    where
        F: FnMut(&mut Write, &FileHash, T) -> Result<()>,
    {
        let mut a = Vec::new();
        f(&mut a, self.hash_a(), arg_a)?;

        let mut b = Vec::new();
        f(&mut b, self.hash_b(), arg_b)?;

        if a == b {
            if !a.is_empty() {
                self.prefix_equal(|state| {
                    state.line(|w, _state| w.write_all(&*a).map_err(From::from))
                })?;
            }
        } else {
            if !a.is_empty() {
                self.prefix_less(|state| {
                    state.line(|w, _state| w.write_all(&*a).map_err(From::from))
                })?;
            }
            if !b.is_empty() {
                self.prefix_greater(|state| {
                    state.line(|w, _state| w.write_all(&*b).map_err(From::from))
                })?;
            }
        }
        Ok(())
    }

    /// This is the same as `Self::line`. It exists for symmetry with `PrintState::line_option`.
    pub fn line_option<F, T>(&mut self, arg_a: T, arg_b: T, f: F) -> Result<()>
    where
        F: FnMut(&mut Write, &FileHash, T) -> Result<()>,
    {
        self.line(arg_a, arg_b, f)
    }

    pub fn line_u64(&mut self, label: &str, arg_a: u64, arg_b: u64) -> Result<()> {
        let base = arg_a;
        self.line_option(arg_a, arg_b, |w, _hash, arg| {
            write!(w, "{}: {}", label, arg)?;
            if arg != base {
                write!(w, " ({:+})", arg as i64 - base as i64)?;
            }
            Ok(())
        })
    }

    pub fn list<T: DiffList>(
        &mut self,
        label: &str,
        arg_a: &T::Arg,
        list_a: &[T],
        arg_b: &T::Arg,
        list_b: &[T],
    ) -> Result<()> {
        if list_a.is_empty() && list_b.is_empty() {
            return Ok(());
        }

        if !label.is_empty() {
            self.line(list_a, list_b, |w, _state, list| {
                if !list.is_empty() {
                    write!(w, "{}:", label)?;
                }
                Ok(())
            })?;
        }

        self.indent(|state| {
            let path = shortest_path(
                list_a,
                list_b,
                |a| a.step_cost(state, arg_a),
                |b| b.step_cost(state, arg_b),
                |a, b| T::diff_cost(state, arg_a, a, arg_b, b),
            );
            let mut iter_a = list_a.iter();
            let mut iter_b = list_b.iter();
            for dir in path {
                match dir {
                    Direction::None => break,
                    Direction::Diagonal => {
                        if let (Some(a), Some(b)) = (iter_a.next(), iter_b.next()) {
                            T::diff(state, arg_a, a, arg_b, b)?;
                        }
                    }
                    Direction::Horizontal => if let Some(a) = iter_a.next() {
                        state.prefix_less(|state| a.print(state, arg_a))?;
                    },
                    Direction::Vertical => if let Some(b) = iter_b.next() {
                        state.prefix_greater(|state| b.print(state, arg_b))?;
                    },
                }
            }
            Ok(())
        })
    }

    // This is similar to `list`, but because the items are ordered
    // we can do a greedy search.
    //
    // The caller must provide lists that are already sorted.
    pub fn ord_list<T: Ord + Print>(
        &mut self,
        label: &str,
        arg_a: &T::Arg,
        list_a: &[T],
        arg_b: &T::Arg,
        list_b: &[T],
    ) -> Result<()> {
        if list_a.is_empty() && list_b.is_empty() {
            return Ok(());
        }

        if !label.is_empty() {
            self.line(list_a, list_b, |w, _state, list| {
                if !list.is_empty() {
                    write!(w, "{}:", label)?;
                }
                Ok(())
            })?;
        }

        self.indent(|state| {
            for item in MergeIterator::new(list_a.iter(), list_b.iter(), T::cmp) {
                match item {
                    MergeResult::Both(a, b) => {
                        T::diff(state, arg_a, a, arg_b, b)?;
                    }
                    MergeResult::Left(a) => {
                        state.prefix_less(|state| a.print(state, arg_a))?;
                    }
                    MergeResult::Right(b) => {
                        state.prefix_greater(|state| b.print(state, arg_b))?;
                    }
                }
            }
            Ok(())
        })
    }

    // This is similar to `list`, but because the items are ordered
    // we can do a greedy search.
    //
    // Items with no difference are not displayed.
    //
    // Also, self.options controls:
    // - sort order
    // - display of added/deleted options
    pub fn sort_list<T: SortList>(
        &mut self,
        arg_a: &T::Arg,
        list_a: &mut [&T],
        arg_b: &T::Arg,
        list_b: &mut [&T],
    ) -> Result<()> {
        list_a.sort_by(|x, y| T::cmp_id_for_sort(&self.hash_a, x, &self.hash_a, y, self.options));
        list_b.sort_by(|x, y| T::cmp_id_for_sort(&self.hash_b, x, &self.hash_b, y, self.options));

        let mut list: Vec<_> = MergeIterator::new(list_a.iter(), list_b.iter(), |a, b| {
            T::cmp_id(&self.hash_a, a, &self.hash_b, b, self.options)
        }).collect();
        list.sort_by(|x, y| {
            MergeResult::cmp(x, y, &self.hash_a, &self.hash_b, |x, hash_x, y, hash_y| {
                T::cmp_by(hash_x, x, hash_y, y, self.options)
            })
        });

        for item in list {
            match item {
                MergeResult::Both(a, b) => {
                    self.diff(|state| T::diff(state, arg_a, a, arg_b, b))?;
                }
                MergeResult::Left(a) => if !self.options.ignore_deleted {
                    self.prefix_less(|state| a.print(state, arg_a))?;
                },
                MergeResult::Right(b) => if !self.options.ignore_added {
                    self.prefix_greater(|state| b.print(state, arg_b))?;
                },
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

enum MergeResult<T> {
    Left(T),
    Right(T),
    Both(T, T),
}

impl<T> MergeResult<T> {
    fn cmp<Arg, F>(x: &Self, y: &Self, arg_left: Arg, arg_right: Arg, f: F) -> cmp::Ordering
    where
        Arg: Copy,
        F: Fn(&T, Arg, &T, Arg) -> cmp::Ordering,
    {
        match x {
            &MergeResult::Both(_, ref x_right) => match y {
                &MergeResult::Both(_, ref y_right) => f(x_right, arg_right, y_right, arg_right),
                &MergeResult::Left(ref y_left) => f(x_right, arg_right, y_left, arg_left),
                &MergeResult::Right(ref y_right) => f(x_right, arg_right, y_right, arg_right),
            },
            &MergeResult::Left(ref x_left) => match y {
                &MergeResult::Both(_, ref y_right) => f(x_left, arg_left, y_right, arg_right),
                &MergeResult::Left(ref y_left) => f(x_left, arg_left, y_left, arg_left),
                &MergeResult::Right(ref y_right) => f(x_left, arg_left, y_right, arg_right),
            },
            &MergeResult::Right(ref x_right) => match y {
                &MergeResult::Both(_, ref y_right) => f(x_right, arg_right, y_right, arg_right),
                &MergeResult::Left(ref y_left) => f(x_right, arg_right, y_left, arg_left),
                &MergeResult::Right(ref y_right) => f(x_right, arg_right, y_right, arg_right),
            },
        }
    }
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
                cost: cost,
                index1: index1,
                index2: index2,
            });
        }
    }

    // Start at the end.  This makes indexing and boundary conditions
    // simpler, and also means we can backtrack in order.
    push(&mut node[len - 1], &mut heap, len1 - 1, len2 - 1, 0, Direction::None);

    while let Some(State {
        index1,
        index2,
        ..
    }) = heap.pop()
    {
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
                push(&mut node[next], &mut heap, index1, next2, cost, Direction::Vertical);
            }
        }
        if index1 > 0 {
            let next1 = index1 - 1;
            let next = index - 1;
            if !node[next].done {
                let cost = node[index].cost + step_cost1(&item1[next1]);
                push(&mut node[next], &mut heap, next1, index2, cost, Direction::Horizontal);
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
                    push(&mut node[next], &mut heap, next1, next2, cost, Direction::Diagonal);
                }
            }
        }
    }

    panic!("failed to find shortest path");
}
