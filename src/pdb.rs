use std::collections::BTreeMap;
use std::io;
use std::rc::Rc;

use crate_pdb as pdb;
use crate_pdb::FallibleIterator;

use super::{Error, Result};
use super::{File, Unit, Namespace, SubprogramOffset, Subprogram, InlinedSubroutine, Variable,
            TypeOffset, Type, TypeKind, BaseType, TypeDef, StructType, UnionType, EnumerationType,
            Enumerator, ArrayType, SubroutineType, TypeModifier, TypeModifierKind, Member,
            Parameter};

pub fn parse(input: &[u8], cb: &mut FnMut(&mut File) -> Result<()>) -> Result<()> {
    let mut cursor = io::Cursor::new(input);
    let mut pdb = pdb::PDB::open(&mut cursor)?;
    let type_information = pdb.type_information()?;
    let symbol_table = pdb.global_symbols()?;

    let mut member_lists = BTreeMap::new();
    let mut enumerator_lists = BTreeMap::new();

    let mut unit = Unit::default();
    let namespace = Namespace::root();

    let mut types = type_information.iter();
    add_primitive_types(&mut unit.types);
    while let Some(ty) = types.next()? {
        let index = ty.type_index() as usize;
        // debug!("Type: {:?}", ty.parse());
        match ty.parse() {
            Ok(pdb::TypeData::Class { properties, fields, size, name, .. }) => {
                // TODO: derived_from, vtable_shape
                parse_class(&mut unit,
                            &member_lists,
                            &namespace,
                            index,
                            properties,
                            fields,
                            size,
                            name)?;
            }
            Ok(pdb::TypeData::Union { properties, fields, size, name, .. }) => {
                parse_union(&mut unit,
                            &member_lists,
                            &namespace,
                            index,
                            properties,
                            fields,
                            size,
                            name)?;
            }
            Ok(pdb::TypeData::Enumeration { properties, underlying_type, fields, name, .. }) => {
                parse_enumeration(&mut unit,
                                  &enumerator_lists,
                                  &namespace,
                                  index,
                                  properties,
                                  underlying_type,
                                  fields,
                                  name)?;
            }
            Ok(pdb::TypeData::Pointer { underlying_type, .. }) => {
                unit.types.insert(index,
                                  Type {
                                      offset: TypeOffset(index),
                                      kind: TypeKind::Modifier(TypeModifier {
                                          kind: TypeModifierKind::Pointer,
                                          ty: Some(TypeOffset(underlying_type as usize)),
                                          name: None,
                                          byte_size: None,
                                      }),
                                  });
            }
            Ok(pdb::TypeData::FieldList { fields, continuation }) => {
                parse_field_list(&mut member_lists,
                                 &mut enumerator_lists,
                                 index,
                                 fields,
                                 continuation)?;
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
            pdb::SymbolData::PublicSymbol { function, offset, .. } => {
                if function {
                    unit.subprograms.insert(symbol_index,
                                            Subprogram {
                                                offset: SubprogramOffset(symbol_index),
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
                                                inlined_subroutines: Vec::new(),
                                                variables: Vec::new(),
                                            });
                    symbol_index += 1;
                }
            }
            _ => {}
        }
    }

    let mut units = Vec::new();
    units.push(unit);

    let mut file = File {
        code: None,
        units: units,
    };

    cb(&mut file)
}

fn add_primitive_types<'input>(types: &mut BTreeMap<usize, Type<'input>>) {
    add_primitive_type(types, 0x00, b"NoType", 4);
    add_primitive_type(types, 0x00, b"void", 0);
    add_primitive_type(types, 0x10, b"i8", 1);  // char
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
    add_primitive_type(types, 0x72, b"i16", 4); // int16_t
    add_primitive_type(types, 0x73, b"u16", 4); // uint16_t
    add_primitive_type(types, 0x74, b"i32", 4); // int32_t
    add_primitive_type(types, 0x75, b"u32", 4); // uint32_t
    add_primitive_type(types, 0x76, b"i64", 8); // int64_t
    add_primitive_type(types, 0x77, b"u64", 8); // uint64_t
}

fn add_primitive_type<'input>(
    types: &mut BTreeMap<usize, Type<'input>>,
    index: usize,
    name: &'static [u8],
    size: u64
) {
    types.insert(index,
                 Type {
                     offset: TypeOffset(index),
                     kind: TypeKind::Base(BaseType {
                         name: Some(name),
                         byte_size: Some(size),
                     }),
                 });

    types.insert(0x400 + index,
                 Type {
                     offset: TypeOffset(0x400 + index),
                     kind: TypeKind::Modifier(TypeModifier {
                         kind: TypeModifierKind::Pointer,
                         ty: Some(TypeOffset(index)),
                         name: None,
                         byte_size: Some(4),
                     }),
                 });

    types.insert(0x600 + index,
                 Type {
                     offset: TypeOffset(0x600 + index),
                     kind: TypeKind::Modifier(TypeModifier {
                         kind: TypeModifierKind::Pointer,
                         ty: Some(TypeOffset(index)),
                         name: None,
                         byte_size: Some(8),
                     }),
                 });
}

fn parse_class<'input>(
    unit: &mut Unit<'input>,
    member_lists: &BTreeMap<usize, Vec<Member<'input>>>,
    namespace: &Rc<Namespace<'input>>,
    index: usize,
    properties: pdb::TypeProperties,
    fields: Option<pdb::TypeIndex>,
    size: u16,
    name: pdb::RawString<'input>
) -> Result<()> {
    let declaration = properties.forward_reference();
    let byte_size = if declaration { None } else { Some(size as u64) };
    let members = match fields {
        Some(fields) => {
            match member_lists.get(&(fields as usize)) {
                Some(members) => members.clone(),
                None => return Err(format!("Missing field list for index {}", fields).into()),
            }
        }
        None => Vec::new(),
    };
    unit.types.insert(index,
                      Type {
                          offset: TypeOffset(index),
                          kind: TypeKind::Struct(StructType {
                              namespace: namespace.clone(),
                              name: Some(name.as_bytes()),
                              byte_size: byte_size,
                              declaration: declaration,
                              members: members,
                          }),
                      });
    Ok(())
}

fn parse_union<'input>(
    unit: &mut Unit<'input>,
    member_lists: &BTreeMap<usize, Vec<Member<'input>>>,
    namespace: &Rc<Namespace<'input>>,
    index: usize,
    properties: pdb::TypeProperties,
    fields: Option<pdb::TypeIndex>,
    size: u32,
    name: pdb::RawString<'input>
) -> Result<()> {
    let declaration = properties.forward_reference();
    let byte_size = if declaration { None } else { Some(size as u64) };
    let members = match fields {
        Some(fields) => {
            match member_lists.get(&(fields as usize)) {
                Some(members) => members.clone(),
                None => return Err(format!("Missing field list for index {}", fields).into()),
            }
        }
        None => Vec::new(),
    };
    unit.types.insert(index,
                      Type {
                          offset: TypeOffset(index),
                          kind: TypeKind::Union(UnionType {
                              namespace: namespace.clone(),
                              name: Some(name.as_bytes()),
                              byte_size: byte_size,
                              declaration: declaration,
                              members: members,
                          }),
                      });
    Ok(())
}

fn parse_enumeration<'input>(
    unit: &mut Unit<'input>,
    enumerator_lists: &BTreeMap<usize, Vec<Enumerator<'input>>>,
    namespace: &Rc<Namespace<'input>>,
    index: usize,
    properties: pdb::TypeProperties,
    _underlying_type: pdb::TypeIndex,
    fields: Option<pdb::TypeIndex>,
    name: pdb::RawString<'input>
) -> Result<()> {
    let declaration = properties.forward_reference();
    let enumerators = match fields {
        Some(fields) => {
            match enumerator_lists.get(&(fields as usize)) {
                Some(enumerators) => enumerators.clone(),
                None => return Err(format!("Missing field list for index {}", fields).into()),
            }
        }
        None => Vec::new(),
    };
    unit.types.insert(index,
                      Type {
                          offset: TypeOffset(index),
                          kind: TypeKind::Enumeration(EnumerationType {
                              namespace: namespace.clone(),
                              name: Some(name.as_bytes()),
                              declaration: declaration,
                              byte_size: None,
                              enumerators: enumerators, // TODO: underlying_type
                          }),
                      });
    Ok(())
}

fn parse_field_list<'input>(
    member_lists: &mut BTreeMap<usize, Vec<Member<'input>>>,
    enumerator_lists: &mut BTreeMap<usize, Vec<Enumerator<'input>>>,
    index: usize,
    fields: Vec<pdb::TypeData<'input>>,
    continuation: Option<pdb::TypeIndex>
) -> Result<()> {
    if continuation.is_some() {
        return Err("Unsupported PDB field list continuation".into());
    }
    let mut members = Vec::new();
    let mut enumerators = Vec::new();
    for field in fields {
        match field {
            pdb::TypeData::Member { field_type, offset, name, .. } => {
                members.push(Member {
                    name: Some(name.as_bytes()),
                    ty: Some(TypeOffset(field_type as usize)),
                    bit_offset: offset as u64 * 8,
                    bit_size: None,
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
