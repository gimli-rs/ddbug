use std::collections::BTreeMap;
use std::io;
use std::rc::Rc;

use crate_pdb as pdb;
use crate_pdb::FallibleIterator;

use Result;
use file::File;
use function::{Function, FunctionOffset, Parameter};
use namespace::Namespace;
use types::{ArrayType, BaseType, EnumerationType, Enumerator, FunctionType, Member, StructType,
            Type, TypeKind, TypeModifier, TypeModifierKind, TypeOffset, UnionType};
use unit::Unit;

pub(crate) fn parse(
    input: &[u8],
    path: &str,
    cb: &mut FnMut(&mut File) -> Result<()>,
) -> Result<()> {
    let mut cursor = io::Cursor::new(input);
    let mut pdb = pdb::PDB::open(&mut cursor)?;
    let type_information = pdb.type_information()?;
    let symbol_table = pdb.global_symbols()?;

    let mut member_lists = BTreeMap::new();
    let mut enumerator_lists = BTreeMap::new();
    let mut argument_lists = BTreeMap::new();
    let mut bitfields = BTreeMap::new();

    let mut unit = Unit::default();
    let namespace = None;

    let mut types = type_information.iter();
    add_primitive_types(&mut unit.types);
    while let Some(ty) = types.next()? {
        let index = ty.type_index() as usize;
        // debug!("Type: {} {:?}", index, ty.parse());
        match ty.parse() {
            Ok(pdb::TypeData::Class(ref data)) => {
                parse_class(&mut unit, &member_lists, &namespace, index, data)?;
            }
            Ok(pdb::TypeData::Union(ref data)) => {
                parse_union(&mut unit, &member_lists, &namespace, index, data)?;
            }
            Ok(pdb::TypeData::Enumeration(ref data)) => {
                parse_enumeration(&mut unit, &enumerator_lists, &namespace, index, data)?;
            }
            Ok(pdb::TypeData::Procedure(ref data)) => {
                parse_procedure(&mut unit, &argument_lists, index, data)?;
            }
            Ok(pdb::TypeData::MemberFunction(ref data)) => {
                parse_member_function(&mut unit, &argument_lists, index, data)?;
            }
            Ok(pdb::TypeData::Pointer(ref data)) => {
                let underlying_type = parse_type_index(data.underlying_type);
                let byte_size = data.attributes.size() as u64;
                let byte_size = if byte_size == 0 {
                    None
                } else {
                    Some(byte_size)
                };
                unit.types.insert(
                    TypeOffset(index),
                    Type {
                        offset: TypeOffset(index),
                        kind: TypeKind::Modifier(TypeModifier {
                            kind: TypeModifierKind::Pointer,
                            ty: underlying_type,
                            name: None,
                            byte_size: byte_size,
                            address_size: None,
                        }),
                    },
                );
            }
            Ok(pdb::TypeData::Modifier(ref data)) => {
                let underlying_type = parse_type_index(data.underlying_type);
                // TODO: volatile, unaligned
                let kind = if data.constant {
                    TypeModifierKind::Const
                } else {
                    TypeModifierKind::Other
                };
                unit.types.insert(
                    TypeOffset(index),
                    Type {
                        offset: TypeOffset(index),
                        kind: TypeKind::Modifier(TypeModifier {
                            kind: kind,
                            ty: underlying_type,
                            name: None,
                            byte_size: None,
                            address_size: None,
                        }),
                    },
                );
            }
            Ok(pdb::TypeData::Bitfield(data)) => {
                bitfields.insert(index, data);
            }
            Ok(pdb::TypeData::Array(ref data)) => {
                parse_array(&mut unit, index, data)?;
            }
            Ok(pdb::TypeData::FieldList(ref data)) => {
                parse_field_list(
                    &mut member_lists,
                    &mut enumerator_lists,
                    &bitfields,
                    index,
                    data,
                )?;
            }
            Ok(pdb::TypeData::ArgumentList(data)) => {
                argument_lists.insert(index, data.arguments);
            }
            Ok(other) => {
                debug!("PDB unimplemented type {} {:?}", index, other);
            }
            Err(pdb::Error::UnimplementedTypeKind(kind)) => {
                debug!("PDB unimplemented type {} {}", index, kind);
            }
            Err(e) => {
                return Err(e.into());
            }
        }
    }

    let mut symbols = symbol_table.iter();
    let mut symbol_index = 0;
    while let Some(symbol) = symbols.next()? {
        match symbol.parse()? {
            pdb::SymbolData::PublicSymbol(data) => if data.function {
                unit.functions.insert(
                    FunctionOffset(symbol_index),
                    Function {
                        namespace: namespace.clone(),
                        name: Some(symbol.name()?.as_bytes()),
                        symbol_name: None,
                        linkage_name: None,
                        source: Default::default(),
                        address: Some(data.offset as u64),
                        size: None,
                        inline: false,
                        declaration: false,
                        parameters: Vec::new(),
                        return_type: None,
                        inlined_functions: Vec::new(),
                        variables: Vec::new(),
                    },
                );
                symbol_index += 1;
            },
            _ => {}
        }
    }

    let mut units = Vec::new();
    units.push(unit);

    let mut file = File {
        path: path,
        // TODO
        code: None,
        // TODO
        sections: Vec::new(),
        // TODO
        symbols: Vec::new(),
        units: units,
    };
    file.normalize();
    cb(&mut file)
}

fn add_primitive_types<'input>(types: &mut BTreeMap<TypeOffset, Type<'input>>) {
    add_primitive_type(types, 0x00, b"NoType", 4);
    add_primitive_type(types, 0x03, b"void", 0);
    add_primitive_type(types, 0x10, b"i8", 1); // signed char
    add_primitive_type(types, 0x11, b"i16", 2); // short
    add_primitive_type(types, 0x12, b"i32", 4); // long
    add_primitive_type(types, 0x13, b"i64", 8);
    add_primitive_type(types, 0x20, b"u8", 1); // unsigned char
    add_primitive_type(types, 0x21, b"u16", 2); // unsigned short
    add_primitive_type(types, 0x22, b"u32", 4); // unsigned long
    add_primitive_type(types, 0x23, b"u64", 8);
    add_primitive_type(types, 0x30, b"bool", 1);
    add_primitive_type(types, 0x40, b"f32", 4); // float
    add_primitive_type(types, 0x41, b"f64", 8); // double
    add_primitive_type(types, 0x68, b"i8", 1); // int8_t
    add_primitive_type(types, 0x69, b"u8", 1); // uint8_t
    add_primitive_type(types, 0x70, b"i8", 1); // char
    add_primitive_type(types, 0x71, b"wchar_t", 2); // wchar_t
    add_primitive_type(types, 0x72, b"i16", 4); // int16_t
    add_primitive_type(types, 0x73, b"u16", 4); // uint16_t
    add_primitive_type(types, 0x74, b"i32", 4); // int32_t
    add_primitive_type(types, 0x75, b"u32", 4); // uint32_t
    add_primitive_type(types, 0x76, b"i64", 8); // int64_t
    add_primitive_type(types, 0x77, b"u64", 8); // uint64_t
}

fn add_primitive_type<'input>(
    types: &mut BTreeMap<TypeOffset, Type<'input>>,
    index: usize,
    name: &'static [u8],
    size: u64,
) {
    types.insert(
        TypeOffset(index),
        Type {
            offset: TypeOffset(index),
            kind: TypeKind::Base(BaseType {
                name: Some(name),
                byte_size: Some(size),
            }),
        },
    );

    types.insert(
        TypeOffset(0x400 + index),
        Type {
            offset: TypeOffset(0x400 + index),
            kind: TypeKind::Modifier(TypeModifier {
                kind: TypeModifierKind::Pointer,
                ty: Some(TypeOffset(index)),
                name: None,
                byte_size: Some(4),
                address_size: None,
            }),
        },
    );

    types.insert(
        TypeOffset(0x600 + index),
        Type {
            offset: TypeOffset(0x600 + index),
            kind: TypeKind::Modifier(TypeModifier {
                kind: TypeModifierKind::Pointer,
                ty: Some(TypeOffset(index)),
                name: None,
                byte_size: Some(8),
                address_size: None,
            }),
        },
    );
}

fn parse_class<'input>(
    unit: &mut Unit<'input>,
    member_lists: &BTreeMap<usize, Vec<Member<'input>>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    index: usize,
    data: &pdb::ClassType<'input>,
) -> Result<()> {
    // TODO: derived_from, vtable_shape
    let fields = data.fields.and_then(parse_type_index);
    let declaration = data.properties.forward_reference();
    let byte_size = if declaration {
        None
    } else {
        Some(data.size as u64)
    };
    let mut members = match fields {
        Some(ref fields) => match member_lists.get(&fields.0) {
            Some(members) => members.clone(),
            None => return Err(format!("Missing field list for index {}", fields.0).into()),
        },
        None => Vec::new(),
    };
    let mut bit_offset = byte_size.map(|v| v * 8);
    for member in members.iter_mut().rev() {
        member.next_bit_offset = bit_offset;
        bit_offset = Some(member.bit_offset);
    }
    unit.types.insert(
        TypeOffset(index),
        Type {
            offset: TypeOffset(index),
            kind: TypeKind::Struct(StructType {
                namespace: namespace.clone(),
                name: Some(data.name.as_bytes()),
                source: Default::default(),
                byte_size: byte_size,
                declaration: declaration,
                members: members,
            }),
        },
    );
    Ok(())
}

fn parse_union<'input>(
    unit: &mut Unit<'input>,
    member_lists: &BTreeMap<usize, Vec<Member<'input>>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    index: usize,
    data: &pdb::UnionType<'input>,
) -> Result<()> {
    let fields = parse_type_index(data.fields);
    let declaration = data.properties.forward_reference();
    let byte_size = if declaration {
        None
    } else {
        Some(data.size as u64)
    };
    let mut members = match fields {
        Some(fields) => match member_lists.get(&fields.0) {
            Some(members) => members.clone(),
            None => return Err(format!("Missing field list for index {}", fields.0).into()),
        },
        None => Vec::new(),
    };
    let mut bit_offset = byte_size.map(|v| v * 8);
    for member in members.iter_mut().rev() {
        member.next_bit_offset = bit_offset;
        bit_offset = Some(member.bit_offset);
    }
    unit.types.insert(
        TypeOffset(index),
        Type {
            offset: TypeOffset(index),
            kind: TypeKind::Union(UnionType {
                namespace: namespace.clone(),
                name: Some(data.name.as_bytes()),
                source: Default::default(),
                byte_size: byte_size,
                declaration: declaration,
                members: members,
            }),
        },
    );
    Ok(())
}

fn parse_enumeration<'input>(
    unit: &mut Unit<'input>,
    enumerator_lists: &BTreeMap<usize, Vec<Enumerator<'input>>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    index: usize,
    data: &pdb::EnumerationType<'input>,
) -> Result<()> {
    let underlying_type = parse_type_index(data.underlying_type);
    let fields = parse_type_index(data.fields);
    let declaration = data.properties.forward_reference();
    let enumerators = match fields {
        Some(ref fields) => match enumerator_lists.get(&fields.0) {
            Some(enumerators) => enumerators.clone(),
            None => return Err(format!("Missing field list for index {}", fields.0).into()),
        },
        None => Vec::new(),
    };
    unit.types.insert(
        TypeOffset(index),
        Type {
            offset: TypeOffset(index),
            kind: TypeKind::Enumeration(EnumerationType {
                namespace: namespace.clone(),
                name: Some(data.name.as_bytes()),
                source: Default::default(),
                declaration: declaration,
                ty: underlying_type,
                byte_size: None,
                enumerators: enumerators,
            }),
        },
    );
    Ok(())
}

fn parse_procedure<'input>(
    unit: &mut Unit<'input>,
    argument_lists: &BTreeMap<usize, Vec<pdb::TypeIndex>>,
    index: usize,
    data: &pdb::ProcedureType,
) -> Result<()> {
    let return_type = data.return_type.and_then(parse_type_index);
    let argument_list = parse_type_index(data.argument_list);
    let parameter_count = data.parameter_count as usize;
    let parameters = match argument_list {
        Some(ref argument_list) => match argument_lists.get(&argument_list.0) {
            Some(arguments) => {
                if arguments.len() != parameter_count {
                    debug!("PDB parameter count mismatch {}, {}", arguments.len(), parameter_count);
                }
                arguments
                    .iter()
                    .map(|argument| {
                        Parameter {
                            offset: None,
                            name: None,
                            ty: parse_type_index(*argument),
                        }
                    })
                    .collect()
            }
            None => return Err(format!("Missing argument list {}", argument_list.0).into()),
        },
        None => Vec::new(),
    };

    unit.types.insert(
        TypeOffset(index),
        // TODO: attributes
        Type {
            offset: TypeOffset(index),
            kind: TypeKind::Function(FunctionType {
                parameters: parameters,
                return_type: return_type,
                byte_size: None,
            }),
        },
    );
    Ok(())
}

fn parse_member_function<'input>(
    unit: &mut Unit<'input>,
    argument_lists: &BTreeMap<usize, Vec<pdb::TypeIndex>>,
    index: usize,
    data: &pdb::MemberFunctionType,
) -> Result<()> {
    let return_type = parse_type_index(data.return_type);
    //let class_type = parse_type_index(data.class_type);
    let this_pointer_type = data.this_pointer_type.and_then(parse_type_index);
    let argument_list = parse_type_index(data.argument_list);
    let parameter_count = data.parameter_count as usize;
    let mut parameters = Vec::with_capacity(parameter_count + 1);
    match this_pointer_type {
        None | Some(TypeOffset(3)) => {}
        ty => {
            parameters.push(Parameter {
                offset: None,
                name: None,
                ty: ty,
            });
        }
    }
    if let Some(ref argument_list) = argument_list {
        match argument_lists.get(&argument_list.0) {
            Some(arguments) => {
                if arguments.len() != parameter_count {
                    debug!("PDB parameter count mismatch {}, {}", arguments.len(), parameter_count);
                }
                for argument in arguments {
                    parameters.push(Parameter {
                        offset: None,
                        name: None,
                        ty: parse_type_index(*argument),
                    });
                }
            }
            None => return Err(format!("Missing argument list {}", argument_list.0).into()),
        }
    };

    unit.types.insert(
        TypeOffset(index),
        // TODO: class_type, attributes, this_adjustment
        Type {
            offset: TypeOffset(index),
            kind: TypeKind::Function(FunctionType {
                parameters: parameters,
                return_type: return_type,
                byte_size: None,
            }),
        },
    );
    Ok(())
}

fn parse_array<'input>(unit: &mut Unit<'input>, index: usize, data: &pdb::ArrayType) -> Result<()> {
    if data.dimensions.len() != 1 {
        return Err("Unsupported multi-dimensional array".into());
    }
    let element_type = parse_type_index(data.element_type);
    //let indexing_type = parse_type_index(indexing_type);
    let byte_size = Some(data.dimensions[0] as u64);
    unit.types.insert(
        TypeOffset(index),
        // TODO: indexing_type, stride
        Type {
            offset: TypeOffset(index),
            kind: TypeKind::Array(ArrayType {
                ty: element_type,
                byte_size: byte_size,
                ..Default::default()
            }),
        },
    );
    Ok(())
}

fn parse_field_list<'input>(
    member_lists: &mut BTreeMap<usize, Vec<Member<'input>>>,
    enumerator_lists: &mut BTreeMap<usize, Vec<Enumerator<'input>>>,
    bitfields: &BTreeMap<usize, pdb::BitfieldType>,
    index: usize,
    data: &pdb::FieldList<'input>,
) -> Result<()> {
    let continuation = data.continuation.and_then(parse_type_index);
    if continuation.is_some() {
        return Err("Unsupported PDB field list continuation".into());
    }
    let mut members = Vec::new();
    let mut enumerators = Vec::new();
    for field in &data.fields {
        match field {
            &pdb::TypeData::Member(ref member) => {
                let mut ty = parse_type_index(member.field_type);
                let mut bit_offset = member.offset as u64 * 8;
                let mut bit_size = None;
                match bitfields.get(&(member.field_type as usize)) {
                    Some(bitfield) => {
                        ty = parse_type_index(bitfield.underlying_type);
                        bit_offset += bitfield.position as u64;
                        bit_size = Some(bitfield.length as u64);
                    }
                    None => {}
                }
                members.push(Member {
                    name: Some(member.name.as_bytes()),
                    ty: ty,
                    bit_offset: bit_offset,
                    bit_size: bit_size,
                    next_bit_offset: None,
                });
            }
            &pdb::TypeData::Enumerate(ref enumerate) => {
                let value = match enumerate.value {
                    pdb::Variant::U8(val) => val as i64,
                    pdb::Variant::U16(val) => val as i64,
                    pdb::Variant::U32(val) => val as i64,
                    pdb::Variant::U64(val) => val as i64,
                    pdb::Variant::I8(val) => val as i64,
                    pdb::Variant::I16(val) => val as i64,
                    pdb::Variant::I32(val) => val as i64,
                    pdb::Variant::I64(val) => val as i64,
                };
                enumerators.push(Enumerator {
                    name: Some(enumerate.name.as_bytes()),
                    value: Some(value),
                });
            }
            _ => {
                debug!("PDB unimplemented field type {:?}", field);
            }
        }
    }
    member_lists.insert(index, members);
    enumerator_lists.insert(index, enumerators);
    Ok(())
}

fn parse_type_index(index: pdb::TypeIndex) -> Option<TypeOffset> {
    if index == 0 {
        None
    } else {
        Some(TypeOffset(index as usize))
    }
}
