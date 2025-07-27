use parser::{Namespace, NamespaceKind};

use crate::Result;
use crate::print::ValuePrinter;

pub(crate) fn print(namespace: &Namespace, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(parent) = namespace.parent() {
        print(parent, w)?;
    }
    w.name(namespace.name().unwrap_or("<anon>"))?;
    if namespace.kind() == NamespaceKind::Function {
        write!(w, "()")?;
    }
    write!(w, "::")?;
    Ok(())
}
