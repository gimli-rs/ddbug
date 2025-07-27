use parser::{Source, Unit};

use crate::Result;
use crate::print::ValuePrinter;

pub(crate) fn print(source: &Source, w: &mut dyn ValuePrinter, unit: &Unit) -> Result<()> {
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
