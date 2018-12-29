use parser::{Source, Unit};

use crate::print::ValuePrinter;
use crate::Result;

pub(crate) fn print(source: &Source, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
    if let Some(path) = source.path(unit) {
        write!(w, "{}", path)?;
        if source.line() != 0 {
            write!(w, ":{}", source.line())?;
            if source.column() != 0 {
                write!(w, ":{}", source.column())?;
            }
        }
    }
    Ok(())
}
