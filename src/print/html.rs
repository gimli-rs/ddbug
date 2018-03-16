use std::io::Write;

use marksman_escape::Escape;

use {Options, Result};
use super::{DiffPrefix, Printer};

const HEADER: &str = r#"<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8"/>
<style>
//li:hover { background: red }
//ul:hover { background: blue }
</style>
<script language="javascript">
window.onload = function () {
    var uls = document.querySelectorAll(".collapsible li ul");
    [].forEach.call(uls, function(ul) {
        ul.style.display = "none"
    });

    var lis = document.querySelectorAll(".collapsible li");
    [].forEach.call(lis, function(li) {
        li.style.cursor = "pointer";
        li.addEventListener("click", toggle);
    });

    function toggle (e) {
        var node = e.target;
        while (node.nodeName !== "LI") {
            node = node.parentNode;
        }
        if (node === e.currentTarget) {
            var uls = node.getElementsByTagName("ul");
            [].forEach.call(uls, function(ul) {
                var li = ul;
                while (li !== null && li.nodeName !== "LI") {
                    li = li.parentNode;
                }
                if (li === node) {
                    if (ul.style.display == "block") {
                        ul.style.display = "none";
                    } else {
                        ul.style.display = "block";
                    }
                }
            });
        }
    }
}
</script>
</head>
<body>
<ul class="collapsible">"#;

const FOOTER: &str = r#"</ul>
</body>
</html>"#;

pub struct HtmlPrinter<'w> {
    w: &'w mut Write,
    indent: usize,
    prefix: DiffPrefix,
    inline_depth: usize,
    line_started: bool,
}

impl<'w> HtmlPrinter<'w> {
    pub fn new(w: &'w mut Write, options: &Options) -> Self {
        HtmlPrinter {
            w,
            indent: 0,
            prefix: DiffPrefix::None,
            inline_depth: options.inline_depth,
            line_started: false,
        }
    }

    pub fn begin(&mut self) -> Result<()> {
        self.w.write_all(HEADER.as_bytes())?;
        Ok(())
    }

    pub fn end(&mut self) -> Result<()> {
        if self.line_started {
            writeln!(self.w, "</li>")?;
        }
        self.w.write_all(FOOTER.as_bytes())?;
        Ok(())
    }
}

impl<'w> Printer for HtmlPrinter<'w> {
    /// Calls `f` to write to a temporary buffer, then only
    /// outputs that buffer if `f` return true.
    fn buffer(&mut self, f: &mut FnMut(&mut Printer) -> Result<bool>) -> Result<bool> {
        let mut buf = Vec::new();
        let ret = {
            let mut p = HtmlPrinter {
                w: &mut buf,
                // TODO: need to ensure these are all unchanged?
                indent: self.indent,
                prefix: self.prefix,
                inline_depth: self.inline_depth,
                line_started: self.line_started,
            };
            f(&mut p)?
        };
        let ret = ret && !buf.is_empty();
        if ret {
            self.w.write_all(&*buf)?;
        }
        Ok(ret)
    }

    fn line_break(&mut self) -> Result<()> {
        Ok(())
    }

    fn line(&mut self, f: &mut FnMut(&mut Write) -> Result<()>) -> Result<()> {
        let mut buf = Vec::new();
        f(&mut buf)?;
        if !buf.is_empty() {
            if self.line_started {
                writeln!(self.w, "</li>")?;
            }
            write!(self.w, "<li>")?;
            self.line_started = true;
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
            self.w.write_all(&*escaped(&*buf))?;
        }
        Ok(())
    }

    fn indent_begin(&mut self) -> Result<()> {
        self.indent += 1;
        writeln!(self.w, "<ul>")?;
        Ok(())
    }

    fn indent_end(&mut self) -> Result<()> {
        self.indent -= 1;
        writeln!(self.w, "</ul>")?;
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

fn escaped(bytes: &[u8]) -> Vec<u8> {
    Escape::new(bytes.iter().map(|x| *x)).collect()
}
