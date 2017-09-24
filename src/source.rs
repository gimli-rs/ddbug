use std::io::Write;

use Result;

#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct Source<'input> {
    pub directory: Option<&'input [u8]>,
    pub file: Option<&'input [u8]>,
    pub line: u64,
    pub column: u64,
}

impl<'input> Source<'input> {
    pub fn is_none(&self) -> bool {
        self.file.is_none()
    }

    pub fn is_some(&self) -> bool {
        self.file.is_some()
    }

    pub fn print(&self, w: &mut Write) -> Result<()> {
        if let Some(file) = self.file {
            if let Some(directory) = self.directory {
                write!(w, "{}/", String::from_utf8_lossy(directory))?;
            }
            write!(w, "{}", String::from_utf8_lossy(file))?;
            if self.line != 0 {
                write!(w, ":{}", self.line)?;
                if self.column != 0 {
                    write!(w, ":{}", self.column)?;
                }
            }
        }
        Ok(())
    }
}
