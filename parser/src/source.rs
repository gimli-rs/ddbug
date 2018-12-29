use crate::unit::Unit;

/// A source location.
#[derive(Debug, Default, Clone)]
pub struct Source<'input> {
    pub(crate) directory: Option<&'input str>,
    pub(crate) file: Option<&'input str>,
    pub(crate) line: u32,
    pub(crate) column: u32,
}

impl<'input> Source<'input> {
    /// The directory.
    ///
    /// This may be absolute, or relative to the working directory of the unit.
    #[inline]
    pub fn directory(&self) -> Option<&str> {
        self.directory
    }

    /// The file name.
    #[inline]
    pub fn file(&self) -> Option<&str> {
        self.file
    }

    /// Return true if there is no file name.
    #[inline]
    pub fn is_none(&self) -> bool {
        self.file.is_none()
    }

    /// Return true if there is a file name.
    #[inline]
    pub fn is_some(&self) -> bool {
        self.file.is_some()
    }

    /// The complete file path.
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

    /// The source line number.
    ///
    /// 0 means unknown line number.
    #[inline]
    pub fn line(&self) -> u32 {
        self.line
    }

    /// The source column number.
    ///
    /// 0 means unknown column number.
    #[inline]
    pub fn column(&self) -> u32 {
        self.column
    }
}
