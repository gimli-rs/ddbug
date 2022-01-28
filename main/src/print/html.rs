use std;
use std::io::Write;

use marksman_escape::Escape;

use super::{DiffPrefix, Printer, ValuePrinter};
use crate::{Options, Result};

const HEADER: &str = r##"<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8"/>
<style>
ul.treeroot {
    list-style: none;
}
ul.treeroot ul {
    list-style: none;
}
ul.treeroot li {
    white-space: nowrap;
    cursor: default;
}
ul.treeroot li.treebranch {
    cursor: pointer;
    border: 1px solid black;
}
ul.treeroot span {
    white-space: normal;
}
ul.treeroot .del {
    background-color: #ffdce0;
}
ul.treeroot .add {
    background-color: #cdffd8;
}
ul.treeroot .mod {
    background-color: #ffffa0;
}
ul.treeroot a {
    color: black;
}
span.field {
    display: inline-block;
    vertical-align: top;
}
</style>
<script language="javascript">
window.onload = function () {
    [].forEach.call(document.querySelectorAll(".treeroot"), function(node) {
        node.addEventListener("click", toggle);
    });

    function toggle (e) {
        var node = e.target;
        while (node.nodeName !== "LI") {
            node = node.parentNode;
            if (node === undefined) {
                return;
            }
        }
        if (!node.classList.contains("treebranch")) {
            return;
        }

        var uls = node.getElementsByTagName("ul");
        var ul = [].find.call(uls, function(ul) {
            var li = ul;
            while (li !== null && li.nodeName !== "LI") {
                li = li.parentNode;
            }
            return li === node;
        });
        if (ul === undefined) {
            return;
        }
        if (node.classList.contains("lazy")) {
            node.classList.remove("lazy");
            fetch('/id/' + node.id)
                .then((response) => { return response.text(); })
                .then((html) => {
                    ul.innerHTML = html;
                    ul.style.display = "block";
                });
        } else {
            if (ul.style.display == "none") {
                ul.style.display = "block";
            } else {
                ul.style.display = "none";
            }
        }
    }
}

function link(anchor, id) {
    // TODO: unit may not have loaded yet
    node = document.getElementById(id);
    if (node !== null) {
        // Find UL
        var uls = node.getElementsByTagName("ul");
        var ul = [].find.call(uls, function(ul) {
            var li = ul;
            while (li !== null && li.nodeName !== "LI") {
                li = li.parentNode;
            }
            return li === node;
        });
        if (ul === undefined) {
            return;
        }
        // Expand node
        if (node.classList.contains("lazy")) {
            node.classList.remove("lazy");
            fetch('/id/' + node.id)
                .then((response) => { return response.text(); })
                .then((html) => {
                    ul.innerHTML = html;
                    done();
                });
        } else {
            done();
        }
        function done() {
            ul.style.display = "block";
            // Display node and parents
            while (node && node.nodeName !== "BODY") {
                if (node.style.display == "none") {
                    node.style.display = "block";
                }
                node = node.parentNode;
            }
            // So that history works nicer
            anchor.scrollIntoView();
            document.location.href = '#' + id;
        }
    }
    return false;
}
</script>
</head>
<body>
<ul class="treeroot">"##;

const FOOTER: &str = r#"</ul>
</body>
</html>"#;

pub struct HtmlPrinter<'w> {
    w: &'w mut dyn Write,
    indent: usize,
    prefix: DiffPrefix,
    inline_depth: usize,
    // Hack to allow indented <ul> to be included within parent <li>.
    line_started: bool,
    http: bool,
}

impl<'w> HtmlPrinter<'w> {
    pub fn new(w: &'w mut dyn Write, options: &Options) -> Self {
        HtmlPrinter {
            w,
            indent: 0,
            prefix: DiffPrefix::None,
            inline_depth: options.inline_depth,
            line_started: false,
            http: options.http,
        }
    }

    pub fn begin(&mut self) -> Result<()> {
        self.w.write_all(HEADER.as_bytes())?;
        Ok(())
    }

    pub fn end(&mut self) -> Result<()> {
        self.w.write_all(FOOTER.as_bytes())?;
        Ok(())
    }
}

impl<'w> Printer for HtmlPrinter<'w> {
    fn value(
        &mut self,
        buf: &mut Vec<u8>,
        f: &mut dyn FnMut(&mut dyn ValuePrinter) -> Result<()>,
    ) -> Result<()> {
        let mut p = HtmlValuePrinter { w: buf };
        f(&mut p)
    }

    /// Calls `f` to write to a temporary buffer.
    fn buffer(
        &mut self,
        buf: &mut Vec<u8>,
        f: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
    ) -> Result<()> {
        let mut p = HtmlPrinter {
            w: buf,
            // TODO: need to ensure these are all unchanged?
            indent: self.indent,
            prefix: self.prefix,
            inline_depth: self.inline_depth,
            line_started: self.line_started,
            http: self.http,
        };
        f(&mut p)?;
        Ok(())
    }

    fn write_buf(&mut self, buf: &[u8]) -> Result<()> {
        self.w.write_all(buf)?;
        Ok(())
    }

    fn line_break(&mut self) -> Result<()> {
        Ok(())
    }

    fn line(&mut self, label: &str, buf: &[u8]) -> Result<()> {
        if !self.line_started {
            write!(self.w, "<li>")?;
        }
        if buf.is_empty() {
            write!(self.w, "<span")?;
            if self.prefix == DiffPrefix::Modify {
                write!(self.w, " class=\"field mod\"")?;
            }
            write!(self.w, ">{}:</span>", label)?;
        } else {
            if !label.is_empty() {
                write!(self.w, "<span class=\"field\">{}:</span> ", label)?;
            }
            write!(self.w, "<span")?;
            match self.prefix {
                DiffPrefix::None | DiffPrefix::Equal => write!(self.w, " class=\"field\"")?,
                DiffPrefix::Modify => {
                    write!(self.w, " class=\"field mod\"")?;
                }
                DiffPrefix::Delete => {
                    write!(self.w, " class=\"field del\"")?;
                }
                DiffPrefix::Add => {
                    write!(self.w, " class=\"field add\"")?;
                }
            }
            write!(self.w, ">")?;
            self.w.write_all(buf)?;
            write!(self.w, "</span>")?;
        }
        if !self.line_started {
            writeln!(self.w, "</li>")?;
        }
        Ok(())
    }

    fn line_diff(&mut self, id: usize, label: &str, a: &[u8], b: &[u8]) -> Result<()> {
        if !self.line_started {
            write!(self.w, "<li>")?;
        }
        if !label.is_empty() {
            write!(self.w, "<span class=\"field\">{}:</span> ", label)?;
        }
        write!(self.w, "<span class=\"field\"")?;
        if id != 0 {
            write!(self.w, " id=\"{}\"", id)?;
        }
        write!(self.w, "><span class=\"del\">")?;
        self.w.write_all(a)?;
        write!(self.w, "</span><br>\n<span class=\"add\">")?;
        self.w.write_all(b)?;
        write!(self.w, "</span></span>")?;
        if !self.line_started {
            writeln!(self.w, "</li>")?;
        }
        Ok(())
    }

    fn indent_body(
        &mut self,
        buf: &mut Vec<u8>,
        body: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
    ) -> Result<()> {
        let mut printer = HtmlPrinter {
            w: buf,
            // TODO: need to ensure these are all unchanged?
            indent: self.indent + 1,
            prefix: self.prefix,
            inline_depth: self.inline_depth,
            line_started: false,
            http: self.http,
        };
        body(&mut printer)?;
        Ok(())
    }

    fn indent_header(
        &mut self,
        collapsed: bool,
        body: &[u8],
        header: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
    ) -> Result<()> {
        debug_assert!(!self.line_started);
        write!(self.w, "<li class=\"treebranch\">")?;
        self.line_started = true;
        header(self)?;
        if collapsed {
            writeln!(self.w, "<ul style=\"display:none\">")?;
        } else {
            writeln!(self.w, "<ul>")?;
        }
        self.write_buf(body)?;
        writeln!(self.w, "</ul></li>")?;
        self.line_started = false;
        Ok(())
    }

    fn indent_id(
        &mut self,
        id: usize,
        header: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
        body: &mut dyn FnMut(&mut dyn Printer) -> Result<()>,
    ) -> Result<()> {
        debug_assert!(!self.line_started);
        write!(
            self.w,
            "<li class=\"treebranch{}\" id=\"{}\">",
            if self.http { " lazy" } else { "" },
            id,
        )?;
        self.line_started = true;
        header(self)?;
        writeln!(self.w, "<ul style=\"display:none\">")?;
        if !self.http {
            body(self)?;
        }
        writeln!(self.w, "</ul></li>")?;
        self.line_started = false;
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

fn escaped(bytes: &[u8]) -> Vec<u8> {
    Escape::new(bytes.iter().cloned()).collect()
}

struct HtmlValuePrinter<'w> {
    w: &'w mut Vec<u8>,
}

impl<'w> Write for HtmlValuePrinter<'w> {
    fn write(&mut self, buf: &[u8]) -> std::result::Result<usize, std::io::Error> {
        self.w.write_all(&*escaped(buf))?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::result::Result<(), std::io::Error> {
        self.w.flush()
    }
}

impl<'w> ValuePrinter for HtmlValuePrinter<'w> {
    fn link(
        &mut self,
        id: usize,
        f: &mut dyn FnMut(&mut dyn ValuePrinter) -> Result<()>,
    ) -> Result<()> {
        if id == 0 {
            f(self)
        } else {
            write!(
                self.w,
                "<a onclick=\"return link(this, \'{}');\" href=\"#{}\">",
                id, id,
            )?;
            f(self)?;
            write!(self.w, "</a>")?;
            Ok(())
        }
    }
}
