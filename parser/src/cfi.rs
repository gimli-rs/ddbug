use crate::Address;
use crate::location::Register;

/// A CFI directive and the function offset it applies to.
///
/// Address::none() is used for directives that apply to the whole function.
pub type Cfi = (Address, CfiDirective);

/// A CFI directive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CfiDirective {
    /// .cfi_startproc
    StartProc,

    /// .cfi_endproc
    EndProc,

    /// .cfi_personality <address>
    Personality(Address),

    /// .cfi_lsda <address>
    // TODO: encoding?
    Lsda(Address),

    /// .cfi_signal_frame
    SignalFrame,

    /// .cfi_return_column <register>
    ReturnColumn(Register),

    /// .cfi_def_cfa <register>, <offset>
    DefCfa(Register, i64),

    /// .cfi_def_cfa_register <register>
    DefCfaRegister(Register),

    /// .cfi_def_cfa_offset <offset>
    DefCfaOffset(i64),

    /// .cfi_offset <register>, <offset>
    Offset(Register, i64),

    /// .cfi_val_offset <register>, <offset>
    ValOffset(Register, i64),

    /// .cfi_register <register1>, <register2>
    Register(Register, Register),

    /// .cfi_restore <register>
    Restore(Register),

    /// .cfi_undefined <register>
    Undefined(Register),

    /// .cfi_same_value <register>
    SameValue(Register),

    /// .cfi_remember_state
    RememberState,

    /// .cfi_restore_state
    RestoreState,

    /// An unsupported instruction.
    Other,
}
