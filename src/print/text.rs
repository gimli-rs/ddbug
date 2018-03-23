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

    fn line(&mut self, buf: &[u8]) -> Result<()> {
        if !buf.is_empty() {
            match self.prefix {
                DiffPrefix::None => {}
                DiffPrefix::Equal => write!(self.w, "  ")?,
                DiffPrefix::Less => {
                    write!(self.w, "- ")?;
                }
                DiffPrefix::Greater => {
                    write!(self.w, "+ ")?;
                }
            }
            for _ in 0..self.indent {
                write!(self.w, "\t")?;
            }
            self.w.write_all(buf)?;
            writeln!(self.w)?;
        }
        Ok(())
    }

    fn line_diff(&mut self, a: &[u8], b: &[u8]) -> Result<()> {
        self.prefix = DiffPrefix::Less;
        self.line(a)?;
        self.prefix = DiffPrefix::Greater;
        self.line(b)
    }

    fn indent(&mut self, body: &mut FnMut(&mut Printer) -> Result<()>) -> Result<()> {
        self.indent += 1;
        body(self)?;
        self.indent -= 1;
        Ok(())
    }

    fn prefix(&mut self, prefix: DiffPrefix) {
        self.prefix = prefix;
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
