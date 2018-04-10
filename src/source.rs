use Result;
use print::ValuePrinter;
use unit::Unit;

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

    pub fn path(&self, unit: &Unit) -> Option<Vec<u8>> {
        fn is_absolute(directory: &[u8]) -> bool {
            directory.get(0) == Some(&b'/') || directory.get(1) == Some(&b':')
        }

        self.file.map(|file| {
            let mut path = Vec::new();
            if let Some(directory) = self.directory {
                if let (false, Some(unit_dir)) = (is_absolute(directory), unit.dir) {
                    path.extend_from_slice(unit_dir);
                    path.push(b'/');
                }
                path.extend_from_slice(directory);
                path.push(b'/');
            }
            path.extend_from_slice(file);
            path
        })
    }

    pub fn print(&self, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
        if let Some(path) = self.path(unit) {
            write!(w, "{}", String::from_utf8_lossy(&*path))?;
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
