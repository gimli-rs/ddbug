# ddbug - Display debugging information 

[![](https://img.shields.io/crates/v/ddbug.svg)](https://crates.io/crates/ddbug) [![](https://docs.rs/ddbug/badge.svg)](https://docs.rs/ddbug/)

`ddbug` is a utility for using DWARF debugging information to explore aspects
code generation, and in particular to see how the code generation changes due
to things such as source code changes or compiler option changes.

Features:
* Type size and layout
* Function size, inlined functions, and functions calls
* Display the differences between two files
* Plain text or HTML output
* Options to filter/sort the plain text output

**This is alpha software. It is likely to contain many bugs and
incomplete features.** Neverthless, it is in a state where it can still
provide some use. Bug reports and feature requests are welcome.

Supports:
* ELF files with DWARF
* Mach-O files with DWARF

## Installing
After installing [Rust](https://www.rust-lang.org/), run:
```
cargo install --git https://github.com/gimli-rs/ddbug
```

## Running

Find the file containing the debugging information, then run:
```
ddbug path-to-file
```

See `ddbug --help` for details on options to control which information
is displayed.

Usually you will want to run `ddbug` on binaries that have been
optimized, but which still contain debugging information. For rust, you
can build your code using:
```
RUSTFLAGS=-g cargo build --release
```

### Diff mode

When given the `--diff` option and two paths to files, `ddbug` will
display the differences between the two binaries. There are some command
line options to specify which differences are considered significant.

## Example output

### struct and union
```
struct core::fmt::Formatter
        size: 96
        members:
                0[16]   width: union core::option::Option<usize>
                16[16]  precision: union core::option::Option<usize>
                32[16]  buf: struct core::fmt::&mut Write
                48[16]  curarg: struct core::slice::Iter<core::fmt::ArgumentV1>
                64[16]  args: struct &[core::fmt::ArgumentV1]
                80[4]   flags: u32
                84[4]   fill: char
                88[1]   align: enum core::fmt::rt::v1::Alignment
                89[7]   <padding>
```

### enum
Note that this is a C style enumeration. Rust enumerations are encoded
in the debugging information as both a union and an enum.
```
enum core::result::Result
        size: 1
        enumerators:
                Ok(0)
                Err(1)
```


### function
```
fn ddbug::main
        linkage name: _ZN5ddbug4mainE
        address: 0x601f0-0x629d9
        size: 10218
        inlined functions:
                [30]    log::__static_max_level
                [59]    log::max_log_level
        calls:
                0x40eee0 env_logger::init
                0x48870 core::result::Result<(), log::SetLoggerError>::ok<(),log::SetLoggerError>

fn log::__static_max_level
        linkage name: _ZN3log18__static_max_levelE
        inline: yes
        return type:
                [8]     enum log::LogLevelFilter
```

## Copyright

Copyright 2016-2018 The ddbug developers

This software is licensed under either of

  * Apache License, Version 2.0 ([`LICENSE-APACHE`](./LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
  * MIT license ([`LICENSE-MIT`](./LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

This software links with a number of libraries, which
have their own licenses. In particular, it links with the
[panopticon](https://github.com/das-labor/panopticon) library, which is
licensed under GPL Version 3.
