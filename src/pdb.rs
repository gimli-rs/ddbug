use std::collections::BTreeMap;
use std::io;
use std::rc::Rc;

use crate_pdb as pdb;
use crate_pdb::FallibleIterator;

use Result;
use {File, Function, FunctionOffset, Namespace, Parameter, Unit};
use types::{ArrayType, BaseType, EnumerationType, Enumerator, FunctionType, Member, StructType,
            Type, TypeKind, TypeModifier, TypeModifierKind, TypeOffset, UnionType};

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
            Ok(pdb::TypeData::Class {
                properties,
                fields,
                size,
                name,
                ..
            }) => {
                // TODO: derived_from, vtable_shape
                let fields = fields.and_then(parse_type_index);
                parse_class(
                    &mut unit,
                    &member_lists,
                    &namespace,
                    index,
                    properties,
                    fields,
                    size,
                    name,
                )?;
            }
            Ok(pdb::TypeData::Union {
                properties,
                fields,
                size,
                name,
                ..
            }) => {
                let fields = parse_type_index(fields);
                parse_union(
                    &mut unit,
                    &member_lists,
                    &namespace,
                    index,
                    properties,
                    fields,
                    size,
                    name,
                )?;
            }
            Ok(pdb::TypeData::Enumeration {
                properties,
                underlying_type,
                fields,
                name,
                ..
            }) => {
                let underlying_type = parse_type_index(underlying_type);
                let fields = parse_type_index(fields);
                parse_enumeration(
                    &mut unit,
                    &enumerator_lists,
                    &namespace,
                    index,
                    properties,
                    underlying_type,
                    fields,
                    name,
                )?;
            }
            Ok(pdb::TypeData::Procedure {
                return_type,
                attributes,
                parameter_count,
                argument_list,
            }) => {
                let return_type = parse_type_index(return_type);
                let argument_list = parse_type_index(argument_list);
                parse_procedure(
                    &mut unit,
                    &argument_lists,
                    index,
                    return_type,
                    attributes,
                    parameter_count,
                    argument_list,
                )?;
            }
            Ok(pdb::TypeData::MemberFunction {
                return_type,
                class_type,
                this_pointer_type,
                attributes,
                parameter_count,
                argument_list,
                this_adjustment,
            }) => {
                let return_type = parse_type_index(return_type);
                let class_type = parse_type_index(class_type);
                let this_pointer_type = parse_type_index(this_pointer_type);
                let argument_list = parse_type_index(argument_list);
                parse_member_function(
                    &mut unit,
                    &argument_lists,
                    index,
                    return_type,
                    class_type,
                    this_pointer_type,
                    attributes,
                    parameter_count,
                    argument_list,
                    this_adjustment,
                )?;
            }
            Ok(pdb::TypeData::Pointer {
                underlying_type,
                attributes,
            }) => {
                let underlying_type = parse_type_index(underlying_type);
                let byte_size = attributes.size() as u64;
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
            Ok(pdb::TypeData::Modifier {
                underlying_type,
                constant,
                ..
            }) => {
                let underlying_type = parse_type_index(underlying_type);
                // TODO: volatile, unaligned
                let kind = if constant {
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
            Ok(pdb::TypeData::Bitfield {
                underlying_type,
                length,
                position,
            }) => {
                bitfields.insert(index, (underlying_type, position, length));
            }
            Ok(pdb::TypeData::Array {
                element_type,
                indexing_type,
                stride,
                dimensions,
            }) => {
                let element_type = parse_type_index(element_type);
                let indexing_type = parse_type_index(indexing_type);
                parse_array(&mut unit, index, element_type, indexing_type, stride, dimensions)?;
            }
            Ok(pdb::TypeData::FieldList {
                fields,
                continuation,
            }) => {
                let continuation = continuation.and_then(parse_type_index);
                parse_field_list(
                    &mut member_lists,
                    &mut enumerator_lists,
                    &bitfields,
                    index,
                    fields,
                    continuation,
                )?;
            }
            Ok(pdb::TypeData::ArgumentList { arguments }) => {
                argument_lists.insert(index, arguments);
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
            pdb::SymbolData::PublicSymbol {
                function, offset, ..
            } => if function {
                unit.functions.insert(
                    FunctionOffset(symbol_index),
                    Function {
                        namespace: namespace.clone(),
                        name: Some(symbol.name()?.as_bytes()),
                        linkage_name: None,
                        low_pc: Some(offset as u64),
                        high_pc: None,
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
        code: None,
        units: units,
    };

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
    properties: pdb::TypeProperties,
    fields: Option<TypeOffset>,
    size: u16,
    name: pdb::RawString<'input>,
) -> Result<()> {
    let declaration = properties.forward_reference();
    let byte_size = if declaration { None } else { Some(size as u64) };
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
                name: Some(name.as_bytes()),
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
    properties: pdb::TypeProperties,
    fields: Option<TypeOffset>,
    size: u32,
    name: pdb::RawString<'input>,
) -> Result<()> {
    let declaration = properties.forward_reference();
    let byte_size = if declaration { None } else { Some(size as u64) };
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
                name: Some(name.as_bytes()),
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
    properties: pdb::TypeProperties,
    underlying_type: Option<TypeOffset>,
    fields: Option<TypeOffset>,
    name: pdb::RawString<'input>,
) -> Result<()> {
    let declaration = properties.forward_reference();
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
                name: Some(name.as_bytes()),
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
    return_type: Option<TypeOffset>,
    _attributes: pdb::FunctionAttributes,
    parameter_count: u16,
    argument_list: Option<TypeOffset>,
) -> Result<()> {
    let parameters = match argument_list {
        Some(ref argument_list) => match argument_lists.get(&argument_list.0) {
            Some(arguments) => {
                if arguments.len() != parameter_count as usize {
                    debug!("PDB parameter count mismatch {}, {}", arguments.len(), parameter_count);
                }
                arguments
                    .iter()
                    .map(|argument| {
                        Parameter {
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
    return_type: Option<TypeOffset>,
    _class_type: Option<TypeOffset>,
    this_pointer_type: Option<TypeOffset>,
    _attributes: pdb::FunctionAttributes,
    parameter_count: u16,
    argument_list: Option<TypeOffset>,
    _this_adjustment: u32,
) -> Result<()> {
    let mut parameters = Vec::with_capacity(parameter_count as usize + 1);
    match this_pointer_type {
        None | Some(TypeOffset(3)) => {}
        ty => {
            parameters.push(Parameter { name: None, ty: ty });
        }
    }
    if let Some(ref argument_list) = argument_list {
        match argument_lists.get(&argument_list.0) {
            Some(arguments) => {
                if arguments.len() != parameter_count as usize {
                    debug!("PDB parameter count mismatch {}, {}", arguments.len(), parameter_count);
                }
                for argument in arguments {
                    parameters.push(Parameter {
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

fn parse_array<'input>(
    unit: &mut Unit<'input>,
    index: usize,
    element_type: Option<TypeOffset>,
    _indexing_type: Option<TypeOffset>,
    _stride: Option<u32>,
    dimensions: Vec<u32>,
) -> Result<()> {
    if dimensions.len() != 1 {
        return Err("Unsupported multi-dimensional array".into());
    }
    let byte_size = Some(dimensions[0] as u64);
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
    bitfields: &BTreeMap<usize, (pdb::TypeIndex, u8, u8)>,
    index: usize,
    fields: Vec<pdb::TypeData<'input>>,
    continuation: Option<TypeOffset>,
) -> Result<()> {
    if continuation.is_some() {
        return Err("Unsupported PDB field list continuation".into());
    }
    let mut members = Vec::new();
    let mut enumerators = Vec::new();
    for field in fields {
        match field {
            pdb::TypeData::Member {
                field_type,
                offset,
                name,
                ..
            } => {
                let mut ty = parse_type_index(field_type);
                let mut bit_offset = offset as u64 * 8;
                let mut bit_size = None;
                match bitfields.get(&(field_type as usize)) {
                    Some(&(bitfield_type, bitfield_offset, bitfield_size)) => {
                        ty = parse_type_index(bitfield_type);
                        bit_offset += bitfield_offset as u64;
                        bit_size = Some(bitfield_size as u64);
                    }
                    None => {}
                }
                members.push(Member {
                    name: Some(name.as_bytes()),
                    ty: ty,
                    bit_offset: bit_offset,
                    bit_size: bit_size,
                    next_bit_offset: None,
                });
            }
            pdb::TypeData::Enumerate { value, name, .. } => {
                let value = match value {
                    pdb::EnumValue::U8(val) => val as i64,
                    pdb::EnumValue::U16(val) => val as i64,
                    pdb::EnumValue::U32(val) => val as i64,
                    pdb::EnumValue::U64(val) => val as i64,
                    pdb::EnumValue::I8(val) => val as i64,
                    pdb::EnumValue::I16(val) => val as i64,
                    pdb::EnumValue::I32(val) => val as i64,
                    pdb::EnumValue::I64(val) => val as i64,
                };
                enumerators.push(Enumerator {
                    name: Some(name.as_bytes()),
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
