use parser::{FunctionCall, Unit};

use crate::print::{Print, ValuePrinter};
use crate::Result;

fn print_header(f: &FunctionCall, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(w, "{:#?}", f)?;
    Ok(())
}

impl<'input> Print for FunctionCall<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut super::PrintState, arg: &Self::Arg) -> parser::Result<()> {
        state.collapsed(
            // TODO: for html, print_size_and_decl includes the function ID,
            // which requires that there are no duplicate functions
            |state| state.line(|w, state| print_header(self, w)),
            |state| Ok(()),
        )?;
        Ok(())
    }

    fn diff(
        state: &mut super::DiffState,
        arg_a: &Self::Arg,
        a: &Self,
        arg_b: &Self::Arg,
        b: &Self,
    ) -> parser::Result<()> {
        todo!()
    }
}
