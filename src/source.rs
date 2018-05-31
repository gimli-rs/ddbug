use Result;
use print::ValuePrinter;
use unit::Unit;

#[derive(Debug, Default, Clone)]
pub(crate) struct Source<'input> {
    pub directory: Option<&'input str>,
    pub file: Option<&'input str>,
    pub line: u64,
    pub column: u64,
}

impl<'input> Source<'input> {
    pub fn directory(&self) -> Option<&str> {
        self.directory
    }

    pub fn file(&self) -> Option<&str> {
        self.file
    }

    pub fn is_none(&self) -> bool {
        self.file.is_none()
    }

    pub fn is_some(&self) -> bool {
        self.file.is_some()
    }

    pub fn path(&self, unit: &Unit) -> Option<String> {
        fn is_absolute(directory: &str) -> bool {
            directory.get(0..1) == Some("/") || directory.get(1..2) == Some(":")
        }

        self.file().map(|file| {
            let mut path = String::new();
            if let Some(directory) = self.directory() {
                if let (false, Some(unit_dir)) = (is_absolute(directory), unit.dir()) {
                    path.push_str(unit_dir);
                    path.push('/');
                }
                path.push_str(directory);
                path.push('/');
            }
            path.push_str(file);
            path
        })
    }

    pub fn print(&self, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
        if let Some(path) = self.path(unit) {
            write!(w, "{}", path)?;
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
