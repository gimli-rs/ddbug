use crate::parser::{Namespace, NamespaceKind};
use crate::print::ValuePrinter;
use crate::Result;

pub(crate) fn print(namespace: &Namespace, w: &mut ValuePrinter) -> Result<()> {
    if let Some(parent) = namespace.parent() {
        print(parent, w)?;
    }
    write!(w, "{}", namespace.name().unwrap_or("<anon>"))?;
    if namespace.kind() == NamespaceKind::Function {
        write!(w, "()")?;
    }
    write!(w, "::")?;
    Ok(())
}
