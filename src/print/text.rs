use std::io::Write;

use {Options, Result};
use super::{DiffPrefix, Printer};

pub struct TextPrinter<'w> {
    w: &'w mut Write,
    indent: usize,
    prefix: DiffPrefix,
    inline_depth: usize,
}

impl<'w> TextPrinter<'w> {
    pub fn new(w: &'w mut Write, options: &Options) -> Self {
        TextPrinter {
            w,
            indent: 0,
            prefix: DiffPrefix::None,
            inline_depth: options.inline_depth,
        }
    }
}

impl<'w> Printer for TextPrinter<'w> {
    /// Calls `f` to write to a temporary buffer.
    fn buffer(
        &mut self,
        buf: &mut Vec<u8>,
        f: &mut FnMut(&mut Printer) -> Result<()>,
    ) -> Result<()> {
        let mut p = TextPrinter {
            w: buf,
            indent: self.indent,
            prefix: self.prefix,
            inline_depth: self.inline_depth,
        };
        f(&mut p)
    }

    fn write_buf(&mut self, buf: &[u8]) -> Result<()> {
        self.w.write_all(buf)?;
        Ok(())
    }

    fn line_break(&mut self) -> Result<()> {
        writeln!(self.w).map_err(From::from)
    }

    fn line(&mut self, label: &str, buf: &[u8]) -> Result<()> {
        match self.prefix {
            DiffPrefix::None => {}
            DiffPrefix::Equal | DiffPrefix::Modify => write!(self.w, "  ")?,
            DiffPrefix::Delete => {
                write!(self.w, "- ")?;
            }
            DiffPrefix::Add => {
                write!(self.w, "+ ")?;
            }
        }
        for _ in 0..self.indent {
            write!(self.w, "\t")?;
        }
        if !label.is_empty() {
            write!(self.w, "{}:", label)?;
            if !buf.is_empty() {
                write!(self.w, " ")?;
            }
        }
        self.w.write_all(buf)?;
        writeln!(self.w)?;
        Ok(())
    }

    fn line_diff(&mut self, label: &str, a: &[u8], b: &[u8]) -> Result<()> {
        self.prefix = DiffPrefix::Delete;
        self.line(label, a)?;
        self.prefix = DiffPrefix::Add;
        self.line(label, b)
    }

    fn indent_body(
        &mut self,
        buf: &mut Vec<u8>,
        body: &mut FnMut(&mut Printer) -> Result<()>,
    ) -> Result<()> {
        let mut printer = TextPrinter {
            w: buf,
            indent: self.indent + 1,
            prefix: self.prefix,
            inline_depth: self.inline_depth,
        };
        body(&mut printer)
    }

    fn indent_header(
        &mut self,
        _collapsed: bool,
        body: &[u8],
        header: &mut FnMut(&mut Printer) -> Result<()>,
    ) -> Result<()> {
        header(self)?;
        self.write_buf(body)?;
        Ok(())
    }

    fn prefix(&mut self, prefix: DiffPrefix) {
        self.prefix = prefix;
    }

    fn get_prefix(&self) -> DiffPrefix {
        self.prefix
    }

    fn inline_begin(&mut self) -> bool {
        if self.inline_depth == 0 {
            false
        } else {
            self.inline_depth -= 1;
            true
        }
    }

    fn inline_end(&mut self) {
        self.inline_depth += 1;
    }
}
