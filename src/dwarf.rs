use std::ffi;
use std::rc::Rc;

use gimli;
use xmas_elf;

use super::Result;
use super::{Unit, Namespace, Subprogram, InlinedSubroutine, Variable, Type, TypeKind, BaseType,
            TypeDef, StructType, UnionType, EnumerationType, Enumerator, ArrayType, SubroutineType,
            UnspecifiedType, PointerToMemberType, TypeModifier, TypeModifierKind, Member, Parameter};

struct DwarfFileState<'input, Endian>
    where Endian: gimli::Endianity
{
    debug_abbrev: gimli::DebugAbbrev<'input, Endian>,
    debug_info: gimli::DebugInfo<'input, Endian>,
    debug_str: gimli::DebugStr<'input, Endian>,
    debug_ranges: gimli::DebugRanges<'input, Endian>,
}

struct DwarfUnitState<'state, 'input, Endian>
    where Endian: 'state + gimli::Endianity,
          'input: 'state
{
    header: &'state gimli::CompilationUnitHeader<'input, Endian>,
    _abbrev: &'state gimli::Abbreviations,
    line: Option<gimli::DebugLineOffset>,
    ranges: Option<gimli::DebugRangesOffset>,
    variables: Vec<DwarfVariable<'input>>,
}

struct DwarfVariable<'input> {
    offset: gimli::UnitOffset,
    specification: Option<gimli::UnitOffset>,
    variable: Variable<'input>,
}

pub fn parse<'input, Endian>(elf: &xmas_elf::ElfFile<'input>) -> Result<Vec<Unit<'input>>>
    where Endian: gimli::Endianity
{
    let debug_abbrev = elf.find_section_by_name(".debug_abbrev").map(|s| s.raw_data(elf));
    let debug_abbrev = gimli::DebugAbbrev::<Endian>::new(debug_abbrev.unwrap_or(&[]));
    let debug_info = elf.find_section_by_name(".debug_info").map(|s| s.raw_data(elf));
    let debug_info = gimli::DebugInfo::<Endian>::new(debug_info.unwrap_or(&[]));
    let debug_str = elf.find_section_by_name(".debug_str").map(|s| s.raw_data(elf));
    let debug_str = gimli::DebugStr::<Endian>::new(debug_str.unwrap_or(&[]));
    let debug_ranges = elf.find_section_by_name(".debug_ranges").map(|s| s.raw_data(elf));
    let debug_ranges = gimli::DebugRanges::<Endian>::new(debug_ranges.unwrap_or(&[]));

    let dwarf = DwarfFileState {
        debug_abbrev: debug_abbrev,
        debug_info: debug_info,
        debug_str: debug_str,
        debug_ranges: debug_ranges,
    };

    let mut units = Vec::new();
    let mut unit_headers = dwarf.debug_info.units();
    while let Some(unit_header) = unit_headers.next()? {
        units.push(parse_unit(&dwarf, &unit_header)?);
    }
    Ok(units)
}

fn parse_unit<'input, Endian>(
    dwarf: &DwarfFileState<'input, Endian>,
    unit_header: &gimli::CompilationUnitHeader<'input, Endian>
) -> Result<Unit<'input>>
    where Endian: gimli::Endianity
{
    let abbrev = &unit_header.abbreviations(dwarf.debug_abbrev)?;
    let mut dwarf_unit = DwarfUnitState {
        header: unit_header,
        _abbrev: abbrev,
        line: None,
        ranges: None,
        variables: Vec::new(),
    };

    let mut tree = unit_header.entries_tree(abbrev, None)?;
    let iter = tree.iter();

    let mut unit = Unit::default();
    unit.address_size = Some(unit_header.address_size() as u64);
    if let Some(entry) = iter.entry() {
        if entry.tag() != gimli::DW_TAG_compile_unit {
            return Err(format!("unknown CU tag: {}", entry.tag()).into());
        }
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    unit.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes)
                }
                gimli::DW_AT_comp_dir => {
                    unit.dir = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes)
                }
                gimli::DW_AT_language => {
                    if let gimli::AttributeValue::Language(language) = attr.value() {
                        unit.language = Some(language);
                    }
                }
                gimli::DW_AT_low_pc => {
                    if let gimli::AttributeValue::Addr(addr) = attr.value() {
                        unit.low_pc = Some(addr);
                    }
                }
                gimli::DW_AT_high_pc => {
                    match attr.value() {
                        gimli::AttributeValue::Addr(addr) => unit.high_pc = Some(addr),
                        gimli::AttributeValue::Udata(size) => unit.size = Some(size),
                        _ => {}
                    }
                }
                gimli::DW_AT_stmt_list => {
                    if let gimli::AttributeValue::DebugLineRef(line) = attr.value() {
                        dwarf_unit.line = Some(line);
                    }
                }
                gimli::DW_AT_ranges => {
                    if let gimli::AttributeValue::DebugRangesRef(ranges) = attr.value() {
                        dwarf_unit.ranges = Some(ranges);
                    }
                }
                gimli::DW_AT_producer |
                gimli::DW_AT_entry_pc |
                gimli::DW_AT_APPLE_optimized |
                gimli::DW_AT_macro_info |
                gimli::DW_AT_sibling => {}
                _ => debug!("unknown CU attribute: {} {:?}", attr.name(), attr.value()),
            }
        }
        debug!("{:?}", unit);
    } else {
        return Err("missing CU entry".into());
    };

    let namespace = None;
    parse_namespace_children(&mut unit, dwarf, &mut dwarf_unit, &namespace, iter)?;

    fixup_variable_specifications(&mut unit, dwarf, &mut dwarf_unit)?;
    Ok(unit)
}

fn fixup_variable_specifications<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    _dwarf: &DwarfFileState<'input, Endian>,
    dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>
) -> Result<()>
    where Endian: gimli::Endianity
{
    loop {
        let mut progress = false;
        let mut defer = Vec::new();

        for mut variable in dwarf_unit.variables.drain(..) {
            match variable.specification.and_then(|v| unit.variables.get(&v.0)) {
                Some(specification) => {
                    let variable = &mut variable.variable;
                    variable.namespace = specification.namespace.clone();
                    if variable.name.is_none() {
                        variable.name = specification.name;
                    }
                    if variable.linkage_name.is_none() {
                        variable.linkage_name = specification.linkage_name;
                    }
                    if variable.ty.is_none() {
                        variable.ty = specification.ty;
                    }
                }
                None => {
                    defer.push(variable);
                    continue;
                }
            }
            unit.variables.insert(variable.offset.0, variable.variable);
            progress = true;
        }

        if defer.is_empty() {
            return Ok(());
        }
        if !progress {
            debug!("invalid specification for {} variables", defer.len());
            for variable in dwarf_unit.variables.drain(..) {
                unit.variables.insert(variable.offset.0, variable.variable);
            }
            return Ok(());
        }
        dwarf_unit.variables = defer;
    }
}

fn parse_namespace_children<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfFileState<'input, Endian>,
    dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<()>
    where Endian: gimli::Endianity
{
    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_namespace => {
                parse_namespace(unit, dwarf, dwarf_unit, namespace, child)?;
            }
            gimli::DW_TAG_subprogram => {
                parse_subprogram(unit, dwarf, dwarf_unit, namespace, child)?;
            }
            gimli::DW_TAG_variable => {
                let variable = parse_variable(unit, dwarf, dwarf_unit, namespace.clone(), child)?;
                if variable.specification.is_some() {
                    // Delay handling specication in case it comes later.
                    dwarf_unit.variables.push(variable);
                } else {
                    unit.variables.insert(variable.offset.0, variable.variable);
                }
            }
            gimli::DW_TAG_imported_declaration |
            gimli::DW_TAG_imported_module => {}
            tag => {
                let offset = child.entry().unwrap().offset();
                if let Some(ty) = parse_type(unit, dwarf, dwarf_unit, namespace, child)? {
                    unit.types.insert(offset.0, ty);
                } else {
                    debug!("unknown namespace child tag: {}", tag);
                }
            }
        }
    }
    Ok(())
}

fn parse_namespace<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfFileState<'input, Endian>,
    dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<()>
    where Endian: gimli::Endianity
{
    let mut name = None;

    {
        let entry = iter.entry().unwrap();
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line => {}
                _ => {
                    debug!("unknown namespace attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    let namespace = Some(Namespace::new(namespace, name));
    parse_namespace_children(unit, dwarf, dwarf_unit, &namespace, iter)
}

fn parse_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfFileState<'input, Endian>,
    dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<Option<Type<'input>>>
    where Endian: gimli::Endianity
{
    let tag = iter.entry().unwrap().tag();
    let mut ty = Type::default();
    ty.offset = iter.entry()
        .unwrap()
        .offset()
        .into();
    ty.kind = match tag {
        gimli::DW_TAG_base_type => {
            TypeKind::Base(parse_base_type(dwarf, dwarf_unit, namespace, iter)?)
        }
        gimli::DW_TAG_typedef => TypeKind::Def(parse_typedef(dwarf, dwarf_unit, namespace, iter)?),
        // TODO: distinguish between class and structure
        gimli::DW_TAG_class_type |
        gimli::DW_TAG_structure_type => {
            TypeKind::Struct(parse_structure_type(unit, dwarf, dwarf_unit, namespace, iter)?)
        }
        gimli::DW_TAG_union_type => {
            TypeKind::Union(parse_union_type(unit, dwarf, dwarf_unit, namespace, iter)?)
        }
        gimli::DW_TAG_enumeration_type => {
            TypeKind::Enumeration(parse_enumeration_type(unit, dwarf, dwarf_unit, namespace, iter)?)
        }
        gimli::DW_TAG_array_type => {
            TypeKind::Array(parse_array_type(dwarf, dwarf_unit, namespace, iter)?)
        }
        gimli::DW_TAG_subroutine_type => {
            TypeKind::Subroutine(parse_subroutine_type(dwarf, dwarf_unit, namespace, iter)?)
        }
        gimli::DW_TAG_unspecified_type => {
            TypeKind::Unspecified(parse_unspecified_type(dwarf, dwarf_unit, namespace, iter)?)
        }
        gimli::DW_TAG_ptr_to_member_type => {
            TypeKind::PointerToMember(parse_pointer_to_member_type(dwarf,
                                                                   dwarf_unit,
                                                                   namespace,
                                                                   iter)?)
        }
        gimli::DW_TAG_pointer_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::Pointer)?)
        }
        gimli::DW_TAG_reference_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::Reference)?)
        }
        gimli::DW_TAG_const_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::Const)?)
        }
        gimli::DW_TAG_packed_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::Packed)?)
        }
        gimli::DW_TAG_volatile_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::Volatile)?)
        }
        gimli::DW_TAG_restrict_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::Restrict)?)
        }
        gimli::DW_TAG_shared_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::Shared)?)
        }
        gimli::DW_TAG_rvalue_reference_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::RvalueReference)?)
        }
        gimli::DW_TAG_atomic_type => {
            TypeKind::Modifier(parse_type_modifier(dwarf,
                                                   dwarf_unit,
                                                   iter,
                                                   TypeModifierKind::Atomic)?)
        }
        _ => return Ok(None),
    };
    Ok(Some(ty))
}

fn parse_type_modifier<'state, 'input, 'abbrev, 'unit, 'tree, Endian>
    (
    dwarf: &DwarfFileState<'input, Endian>,
     _unit: &mut DwarfUnitState<'state, 'input, Endian>,
     mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>,
     kind: TypeModifierKind
) -> Result<TypeModifier<'input>>
    where Endian: gimli::Endianity
{
    let mut modifier = TypeModifier {
        kind: kind,
        ty: None,
        name: None,
        byte_size: None,
    };

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    modifier.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        modifier.ty = Some(offset.into());
                    }
                }
                gimli::DW_AT_byte_size => {
                    modifier.byte_size = attr.udata_value();
                }
                _ => {
                    debug!("unknown type modifier attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown type modifier child tag: {}", tag);
            }
        }
    }
    Ok(modifier)
}

fn parse_base_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfFileState<'input, Endian>,
    _unit: &mut DwarfUnitState<'state, 'input, Endian>,
    _namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<BaseType<'input>>
    where Endian: gimli::Endianity
{
    let mut ty = BaseType::default();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                gimli::DW_AT_encoding => {}
                _ => {
                    debug!("unknown base type attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown base type child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_typedef<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfFileState<'input, Endian>,
    _unit: &mut DwarfUnitState<'state, 'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<TypeDef<'input>>
    where Endian: gimli::Endianity
{
    let mut typedef = TypeDef::default();
    typedef.namespace = namespace.clone();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    typedef.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        typedef.ty = Some(offset.into());
                    }
                }
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line => {}
                _ => {
                    debug!("unknown typedef attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown typedef child tag: {}", tag);
            }
        }
    }
    Ok(typedef)
}

fn parse_structure_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>
    (
    unit: &mut Unit<'input>,
     dwarf: &DwarfFileState<'input, Endian>,
     dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
     namespace: &Option<Rc<Namespace<'input>>>,
     mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<StructType<'input>>
    where Endian: gimli::Endianity
{
    let mut ty = StructType::default();
    ty.namespace = namespace.clone();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                gimli::DW_AT_declaration => {
                    if let gimli::AttributeValue::Flag(flag) = attr.value() {
                        ty.declaration = flag;
                    }
                }
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line |
                gimli::DW_AT_containing_type |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown struct attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    let namespace = Some(Namespace::new(&ty.namespace, ty.name));
    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_subprogram => {
                parse_subprogram(unit, dwarf, dwarf_unit, &namespace, child)?;
            }
            gimli::DW_TAG_member => {
                parse_member(&mut ty.members, unit, dwarf, dwarf_unit, &namespace, child)?;
            }
            gimli::DW_TAG_inheritance |
            gimli::DW_TAG_template_type_parameter |
            gimli::DW_TAG_template_value_parameter |
            gimli::DW_TAG_GNU_template_parameter_pack => {}
            tag => {
                let offset = child.entry().unwrap().offset();
                if let Some(ty) = parse_type(unit, dwarf, dwarf_unit, &namespace, child)? {
                    unit.types.insert(offset.0, ty);
                } else {
                    debug!("unknown struct child tag: {}", tag);
                }
            }
        }
    }
    Ok(ty)
}

fn parse_union_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfFileState<'input, Endian>,
    dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<UnionType<'input>>
    where Endian: gimli::Endianity
{
    let mut ty = UnionType::default();
    ty.namespace = namespace.clone();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                gimli::DW_AT_declaration => {
                    if let gimli::AttributeValue::Flag(flag) = attr.value() {
                        ty.declaration = flag;
                    }
                }
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown union attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    let namespace = Some(Namespace::new(&ty.namespace, ty.name));
    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_subprogram => {
                parse_subprogram(unit, dwarf, dwarf_unit, &namespace, child)?;
            }
            gimli::DW_TAG_member => {
                parse_member(&mut ty.members, unit, dwarf, dwarf_unit, &namespace, child)?;
            }
            gimli::DW_TAG_template_type_parameter => {}
            tag => {
                let offset = child.entry().unwrap().offset();
                if let Some(ty) = parse_type(unit, dwarf, dwarf_unit, &namespace, child)? {
                    unit.types.insert(offset.0, ty);
                } else {
                    debug!("unknown union child tag: {}", tag);
                }
            }
        }
    }
    Ok(ty)
}

fn parse_member<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    members: &mut Vec<Member<'input>>,
    unit: &mut Unit<'input>,
    dwarf: &DwarfFileState<'input, Endian>,
    dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<()>
    where Endian: gimli::Endianity
{
    let mut member = Member::default();
    let mut bit_offset = None;
    let mut byte_size = None;
    let mut declaration = false;

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    member.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        member.ty = Some(offset.into());
                    }
                }
                gimli::DW_AT_data_member_location => {
                    match attr.value() {
                        gimli::AttributeValue::Udata(v) => member.bit_offset = v * 8,
                        gimli::AttributeValue::Sdata(v) => {
                            if v >= 0 {
                                member.bit_offset = (v as u64) * 8;
                            } else {
                                debug!("DW_AT_data_member_location is negative: {}", v)
                            }
                        }
                        gimli::AttributeValue::Exprloc(expr) => {
                            match evaluate(dwarf_unit.header, expr) {
                                Ok(gimli::Location::Address { address }) => {
                                    member.bit_offset = address * 8;
                                }
                                Ok(loc) => {
                                    debug!("unknown DW_AT_data_member_location result: {:?}", loc)
                                }
                                Err(e) => {
                                    debug!("DW_AT_data_member_location evaluation failed: {}", e)
                                }
                            }
                        }
                        gimli::AttributeValue::DebugLocRef(..) => {
                            // TODO
                        }
                        _ => {
                            debug!("unknown DW_AT_data_member_location: {:?}", attr.value());
                        }
                    }
                }
                gimli::DW_AT_data_bit_offset => {
                    if let Some(bit_offset) = attr.udata_value() {
                        member.bit_offset = bit_offset;
                    }
                }
                gimli::DW_AT_bit_offset => {
                    bit_offset = attr.udata_value();
                }
                gimli::DW_AT_byte_size => {
                    byte_size = attr.udata_value();
                }
                gimli::DW_AT_bit_size => {
                    member.bit_size = attr.udata_value();
                }
                gimli::DW_AT_declaration => {
                    declaration = true;
                }
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line |
                gimli::DW_AT_external |
                gimli::DW_AT_accessibility |
                gimli::DW_AT_artificial |
                gimli::DW_AT_const_value |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown member attribute: {} {:?}",
                           attr.name(),
                           attr.value());
                }
            }
        }
    }

    if declaration {
        // This is a C++ static data member. Parse it as a variable instead.
        // Note: the DWARF 5 standard says static members should use DW_TAG_variable,
        // but at least clang 3.7.1 uses DW_TAG_member.
        let variable = parse_variable(unit, dwarf, dwarf_unit, namespace.clone(), iter)?;
        if variable.specification.is_some() {
            debug!("specification on variable declaration at offset 0x{:x}",
                   variable.offset.0);
        }
        unit.variables.insert(variable.offset.0, variable.variable);
        return Ok(());
    }

    if let (Some(bit_offset), Some(bit_size)) = (bit_offset, member.bit_size) {
        // DWARF version 2/3, but allowed in later versions for compatibility.
        // The data member is a bit field contained in an anonymous object.
        // member.bit_offset starts as the offset of the anonymous object.
        // byte_size is the size of the anonymous object.
        // bit_offset is the offset from the anonymous object MSB to the bit field MSB.
        // bit_size is the size of the bit field.
        if Endian::is_big_endian() {
            // For big endian, the MSB is the first bit, so we simply add bit_offset,
            // and byte_size is unneeded.
            member.bit_offset = member.bit_offset.wrapping_add(bit_offset);
        } else {
            // For little endian, we have to work backwards, so we need byte_size.
            if let Some(byte_size) = byte_size {
                // First find the offset of the MSB of the anonymous object.
                member.bit_offset = member.bit_offset.wrapping_add(byte_size * 8);
                // Then go backwards to the LSB of the bit field.
                member.bit_offset = member.bit_offset
                    .wrapping_sub(bit_offset.wrapping_add(bit_size));
            } else {
                // DWARF version 2/3 says the byte_size can be inferred,
                // but it is unclear when this would be useful.
                // Delay implementing this until needed.
                debug!("missing byte_size for bit field offset");
            }
        }
    } else if byte_size.is_some() {
        // TODO: should this set member.bit_size?
        debug!("ignored member byte_size");
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown member child tag: {}", tag);
            }
        }
    }
    members.push(member);
    Ok(())
}

fn parse_enumeration_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>
    (
    unit: &mut Unit<'input>,
     dwarf: &DwarfFileState<'input, Endian>,
     dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
     namespace: &Option<Rc<Namespace<'input>>>,
     mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<EnumerationType<'input>>
    where Endian: gimli::Endianity
{
    let mut ty = EnumerationType::default();
    ty.namespace = namespace.clone();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                gimli::DW_AT_declaration => {
                    if let gimli::AttributeValue::Flag(flag) = attr.value() {
                        ty.declaration = flag;
                    }
                }
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line |
                gimli::DW_AT_sibling |
                gimli::DW_AT_type |
                gimli::DW_AT_enum_class => {}
                _ => {
                    debug!("unknown enumeration attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    let namespace = Some(Namespace::new(&ty.namespace, ty.name));
    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_enumerator => {
                ty.enumerators.push(parse_enumerator(dwarf, dwarf_unit, &namespace, child)?);
            }
            gimli::DW_TAG_subprogram => {
                parse_subprogram(unit, dwarf, dwarf_unit, &namespace, child)?;
            }
            tag => {
                debug!("unknown enumeration child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_enumerator<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfFileState<'input, Endian>,
    _dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    _namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<Enumerator<'input>>
    where Endian: gimli::Endianity
{
    let mut enumerator = Enumerator::default();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(ref attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    enumerator.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_const_value => {
                    if let Some(value) = attr.sdata_value() {
                        enumerator.value = Some(value);
                    } else {
                        debug!("unknown enumerator const_value: {:?}", attr.value());
                    }
                }
                _ => {
                    debug!("unknown enumerator attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown enumerator child tag: {}", tag);
            }
        }
    }
    Ok(enumerator)
}

fn parse_array_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    _dwarf: &DwarfFileState<'input, Endian>,
    _dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    _namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<ArrayType<'input>>
    where Endian: gimli::Endianity
{
    let mut array = ArrayType::default();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        array.ty = Some(offset.into());
                    }
                }
                gimli::DW_AT_GNU_vector |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown array attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_subrange_type => {
                let mut attrs = child.entry().unwrap().attrs();
                while let Some(attr) = attrs.next()? {
                    match attr.name() {
                        gimli::DW_AT_count => {
                            array.count = attr.udata_value();
                        }
                        gimli::DW_AT_upper_bound => {
                            // TODO: use AT_lower_bound too
                            array.count = attr.udata_value().map(|v| v + 1);
                        }
                        gimli::DW_AT_type |
                        gimli::DW_AT_lower_bound => {}
                        _ => {
                            debug!("unknown array subrange attribute: {} {:?}",
                                   attr.name(),
                                   attr.value())
                        }
                    }
                }
            }
            tag => {
                debug!("unknown array child tag: {}", tag);
            }
        }
    }
    Ok(array)
}

fn parse_subroutine_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>
    (
    dwarf: &DwarfFileState<'input, Endian>,
     dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
     _namespace: &Option<Rc<Namespace<'input>>>,
     mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<SubroutineType<'input>>
    where Endian: gimli::Endianity
{
    let mut subroutine = SubroutineType::default();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        subroutine.return_type = Some(offset.into());
                    }
                }
                gimli::DW_AT_prototyped |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown subroutine attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_formal_parameter => {
                subroutine.parameters.push(parse_parameter(dwarf, dwarf_unit, child)?);
            }
            tag => {
                debug!("unknown subroutine child tag: {}", tag);
            }
        }
    }
    Ok(subroutine)
}

fn parse_unspecified_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>
    (
    dwarf: &DwarfFileState<'input, Endian>,
     _dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
     namespace: &Option<Rc<Namespace<'input>>>,
     mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<UnspecifiedType<'input>>
    where Endian: gimli::Endianity
{
    let mut ty = UnspecifiedType::default();
    ty.namespace = namespace.clone();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                _ => {
                    debug!("unknown unspecified type attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown unspecified type child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_pointer_to_member_type<'state, 'input, 'abbrev, 'unit, 'tree, Endian>
    (
    _dwarf: &DwarfFileState<'input, Endian>,
     _dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
     _namespace: &Option<Rc<Namespace<'input>>>,
     mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<PointerToMemberType>
    where Endian: gimli::Endianity
{
    let mut ty = PointerToMemberType::default();

    {
        let mut attrs = iter.entry().unwrap().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        ty.ty = Some(offset.into());
                    }
                }
                gimli::DW_AT_containing_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        ty.containing_ty = Some(offset.into());
                    }
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                _ => {
                    debug!("unknown ptr_to_member type attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown ptr_to_member type child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_subprogram<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfFileState<'input, Endian>,
    dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<()>
    where Endian: gimli::Endianity
{
    let mut subprogram = Subprogram {
        offset: iter.entry()
            .unwrap()
            .offset()
            .into(),
        namespace: namespace.clone(),
        name: None,
        linkage_name: None,
        low_pc: None,
        high_pc: None,
        size: None,
        inline: false,
        declaration: false,
        parameters: Vec::new(),
        return_type: None,
        inlined_subroutines: Vec::new(),
        variables: Vec::new(),
    };

    let mut specification = None;

    {
        let entry = iter.entry().unwrap();
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    subprogram.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_linkage_name |
                gimli::DW_AT_MIPS_linkage_name => {
                    subprogram.linkage_name = attr.string_value(&dwarf.debug_str)
                        .map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_inline => {
                    if let gimli::AttributeValue::Inline(val) = attr.value() {
                        match val {
                            gimli::DW_INL_inlined |
                            gimli::DW_INL_declared_inlined => subprogram.inline = true,
                            _ => subprogram.inline = false,
                        }
                    }
                }
                gimli::DW_AT_low_pc => {
                    if let gimli::AttributeValue::Addr(addr) = attr.value() {
                        subprogram.low_pc = Some(addr);
                    }
                }
                gimli::DW_AT_high_pc => {
                    match attr.value() {
                        gimli::AttributeValue::Addr(addr) => subprogram.high_pc = Some(addr),
                        gimli::AttributeValue::Udata(size) => subprogram.size = Some(size),
                        _ => {}
                    }
                }
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        subprogram.return_type = Some(offset.into());
                    }
                }
                gimli::DW_AT_specification => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        specification = Some(offset);
                    }
                }
                gimli::DW_AT_declaration => {
                    if let gimli::AttributeValue::Flag(flag) = attr.value() {
                        subprogram.declaration = flag;
                    }
                }
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line |
                gimli::DW_AT_frame_base |
                gimli::DW_AT_external |
                gimli::DW_AT_abstract_origin |
                gimli::DW_AT_GNU_all_call_sites |
                gimli::DW_AT_GNU_all_tail_call_sites |
                gimli::DW_AT_prototyped |
                gimli::DW_AT_accessibility |
                gimli::DW_AT_explicit |
                gimli::DW_AT_artificial |
                gimli::DW_AT_object_pointer |
                gimli::DW_AT_virtuality |
                gimli::DW_AT_vtable_elem_location |
                gimli::DW_AT_containing_type |
                gimli::DW_AT_APPLE_optimized |
                gimli::DW_AT_APPLE_omit_frame_ptr |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown subprogram attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }

        if let Some(specification) = specification {
            match unit.subprograms.get(&specification.0) {
                Some(specification) => {
                    subprogram.namespace = specification.namespace.clone();
                    if subprogram.name.is_none() {
                        subprogram.name = specification.name;
                    }
                    if subprogram.linkage_name.is_none() {
                        subprogram.linkage_name = specification.linkage_name;
                    }
                    // TODO: will these ever be present in the specification?
                    if subprogram.low_pc.is_none() {
                        subprogram.low_pc = specification.low_pc;
                    }
                    if subprogram.high_pc.is_none() {
                        subprogram.high_pc = specification.high_pc;
                    }
                    if subprogram.size.is_none() {
                        subprogram.size = specification.size;
                    }
                    if subprogram.return_type.is_none() {
                        subprogram.return_type = specification.return_type;
                    }
                    // TODO: inline?
                    // TODO: parameters?
                }
                None => {
                    // TODO: this may occur if specification comes later
                    debug!("invalid subprogram offset: 0x{:x}", specification.0);
                }
            }
        }

        if let Some(low_pc) = subprogram.low_pc {
            if let Some(high_pc) = subprogram.high_pc {
                subprogram.size = high_pc.checked_sub(low_pc);
            } else if let Some(size) = subprogram.size {
                subprogram.high_pc = low_pc.checked_add(size);
            }
        }
    }

    let namespace = Some(Namespace::new(&subprogram.namespace, subprogram.name));
    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_formal_parameter => {
                subprogram.parameters.push(parse_parameter(dwarf, dwarf_unit, child)?);
            }
            gimli::DW_TAG_inlined_subroutine => {
                subprogram.inlined_subroutines.push(parse_inlined_subroutine(unit,
                                                                             dwarf,
                                                                             dwarf_unit,
                                                                             child)?);
            }
            gimli::DW_TAG_variable => {
                let variable = parse_variable(unit, dwarf, dwarf_unit, None, child)?;
                if variable.specification.is_some() {
                    debug!("specification on subprogram declaration at offset 0x{:x}",
                           variable.offset.0);
                }
                subprogram.variables.push(variable.variable);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block(&mut subprogram.inlined_subroutines,
                                    &mut subprogram.variables,
                                    unit,
                                    dwarf,
                                    dwarf_unit,
                                    child)?;
            }
            gimli::DW_TAG_unspecified_parameters |
            gimli::DW_TAG_template_type_parameter |
            gimli::DW_TAG_template_value_parameter |
            gimli::DW_TAG_GNU_template_parameter_pack |
            gimli::DW_TAG_label |
            gimli::DW_TAG_imported_declaration |
            gimli::DW_TAG_imported_module |
            gimli::DW_TAG_GNU_call_site => {}
            tag => {
                let offset = child.entry().unwrap().offset();
                if let Some(ty) = parse_type(unit, dwarf, dwarf_unit, &namespace, child)? {
                    unit.types.insert(offset.0, ty);
                } else {
                    debug!("unknown subprogram child tag: {}", tag);
                }
            }
        }
    }

    unit.subprograms.insert(subprogram.offset.0, subprogram);
    Ok(())
}

fn parse_parameter<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfFileState<'input, Endian>,
    _unit: &mut DwarfUnitState<'state, 'input, Endian>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<Parameter<'input>>
    where Endian: gimli::Endianity
{
    let mut parameter = Parameter::default();

    {
        let entry = iter.entry().unwrap();
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    parameter.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        parameter.ty = Some(offset.into());
                    }
                }
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line |
                gimli::DW_AT_location |
                gimli::DW_AT_abstract_origin |
                gimli::DW_AT_artificial |
                gimli::DW_AT_const_value |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown parameter attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown parameter child tag: {}", tag);
            }
        }
    }
    Ok(parameter)
}

fn parse_lexical_block<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    inlined_subroutines: &mut Vec<InlinedSubroutine<'input>>,
    variables: &mut Vec<Variable<'input>>,
    unit: &mut Unit<'input>,
    dwarf: &DwarfFileState<'input, Endian>,
    dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<()>
    where Endian: gimli::Endianity
{
    {
        let entry = iter.entry().unwrap();
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_low_pc |
                gimli::DW_AT_high_pc |
                gimli::DW_AT_ranges |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown lexical_block attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_inlined_subroutine => {
                inlined_subroutines.push(parse_inlined_subroutine(unit, dwarf, dwarf_unit, child)?);
            }
            gimli::DW_TAG_variable => {
                let variable = parse_variable(unit, dwarf, dwarf_unit, None, child)?;
                if variable.specification.is_some() {
                    debug!("specification on subprogram declaration at offset 0x{:x}",
                           variable.offset.0);
                }
                variables.push(variable.variable);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block(inlined_subroutines,
                                    variables,
                                    unit,
                                    dwarf,
                                    dwarf_unit,
                                    child)?;
            }
            gimli::DW_TAG_formal_parameter |
            gimli::DW_TAG_label |
            gimli::DW_TAG_imported_declaration |
            gimli::DW_TAG_imported_module => {}
            tag => {
                debug!("unknown lexical_block child tag: {}", tag);
            }
        }
    }
    Ok(())
}

fn parse_inlined_subroutine<'state, 'input, 'abbrev, 'unit, 'tree, Endian>
    (
    unit: &mut Unit<'input>,
     dwarf: &DwarfFileState<'input, Endian>,
     dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
     mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<InlinedSubroutine<'input>>
    where Endian: gimli::Endianity
{
    let mut subroutine = InlinedSubroutine::default();
    let mut low_pc = None;
    let mut high_pc = None;
    let mut size = None;
    let mut ranges = None;
    {
        let entry = iter.entry().unwrap();
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_abstract_origin => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        subroutine.abstract_origin = Some(offset.into());
                    }
                }
                gimli::DW_AT_low_pc => {
                    if let gimli::AttributeValue::Addr(addr) = attr.value() {
                        low_pc = Some(addr);
                    }
                }
                gimli::DW_AT_high_pc => {
                    match attr.value() {
                        gimli::AttributeValue::Addr(addr) => high_pc = Some(addr),
                        gimli::AttributeValue::Udata(val) => size = Some(val),
                        _ => {}
                    }
                }
                gimli::DW_AT_ranges => {
                    if let gimli::AttributeValue::DebugRangesRef(val) = attr.value() {
                        ranges = Some(val);
                    }
                }
                gimli::DW_AT_call_file |
                gimli::DW_AT_call_line |
                gimli::DW_AT_entry_pc |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown inlined_subroutine attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    if let Some(offset) = ranges {
        let mut size = 0;
        let low_pc = low_pc.unwrap_or(0);
        let mut ranges = dwarf.debug_ranges
            .ranges(offset, dwarf_unit.header.address_size(), low_pc)?;
        while let Some(range) = ranges.next()? {
            size += range.end.wrapping_sub(range.begin);
        }
        subroutine.size = Some(size);
    } else if let Some(size) = size {
        subroutine.size = Some(size);
    } else if let (Some(low_pc), Some(high_pc)) = (low_pc, high_pc) {
        subroutine.size = Some(high_pc.wrapping_sub(low_pc));
    } else {
        debug!("unknown inlined_subroutine size");
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_inlined_subroutine => {
                subroutine.inlined_subroutines.push(parse_inlined_subroutine(unit,
                                                                             dwarf,
                                                                             dwarf_unit,
                                                                             child)?);
            }
            gimli::DW_TAG_variable => {
                let variable = parse_variable(unit, dwarf, dwarf_unit, None, child)?;
                subroutine.variables.push(variable.variable);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block(&mut subroutine.inlined_subroutines,
                                    &mut subroutine.variables,
                                    unit,
                                    dwarf,
                                    dwarf_unit,
                                    child)?;
            }
            gimli::DW_TAG_formal_parameter => {}
            tag => {
                debug!("unknown inlined_subroutine child tag: {}", tag);
            }
        }
    }
    Ok(subroutine)
}

fn parse_variable<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    _unit: &mut Unit<'input>,
    dwarf: &DwarfFileState<'input, Endian>,
    _dwarf_unit: &mut DwarfUnitState<'state, 'input, Endian>,
    namespace: Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<DwarfVariable<'input>>
    where Endian: gimli::Endianity
{
    let offset = iter.entry().unwrap().offset();
    let mut specification = None;
    let mut variable = Variable::default();
    variable.namespace = namespace;

    {
        let entry = iter.entry().unwrap();
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    variable.name = attr.string_value(&dwarf.debug_str).map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_linkage_name |
                gimli::DW_AT_MIPS_linkage_name => {
                    variable.linkage_name = attr.string_value(&dwarf.debug_str)
                        .map(ffi::CStr::to_bytes);
                }
                gimli::DW_AT_type => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        variable.ty = Some(offset.into());
                    }
                }
                gimli::DW_AT_specification => {
                    if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                        specification = Some(offset);
                    }
                }
                gimli::DW_AT_declaration => {
                    if let gimli::AttributeValue::Flag(flag) = attr.value() {
                        variable.declaration = flag;
                    }
                }
                gimli::DW_AT_abstract_origin |
                gimli::DW_AT_artificial |
                gimli::DW_AT_const_value |
                gimli::DW_AT_location |
                gimli::DW_AT_external |
                gimli::DW_AT_accessibility |
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line => {}
                _ => {
                    debug!("unknown variable attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = iter.next()? {
        match child.entry().unwrap().tag() {
            tag => {
                debug!("unknown variable child tag: {}", tag);
            }
        }
    }

    Ok(DwarfVariable {
           offset: offset,
           specification: specification,
           variable: variable,
       })
}


fn evaluate<'input, Endian>(
    unit: &gimli::CompilationUnitHeader<Endian>,
    bytecode: gimli::EndianBuf<'input, Endian>
) -> Result<gimli::Location<'input>>
    where Endian: gimli::Endianity + 'input
{
    let mut evaluation =
        gimli::Evaluation::<Endian>::new(bytecode, unit.address_size(), unit.format());
    evaluation.set_initial_value(0);
    let result = evaluation.evaluate()?;
    match result {
        gimli::EvaluationResult::Complete => {
            let pieces = evaluation.result();
            if pieces.len() != 1 {
                return Err(format!("unsupported number of evaluation pieces: {}", pieces.len())
                               .into());
            }
            Ok(pieces[0].location)
        }
        _ => Err("unsupported evaluation expression".into()),
    }
}
