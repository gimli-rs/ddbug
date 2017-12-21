# ddbug - Display debugging information 

[![](https://img.shields.io/crates/v/ddbug.svg)](https://crates.io/crates/ddbug) [![](https://docs.rs/ddbug/badge.svg)](https://docs.rs/ddbug/)

`ddbug` is a utility that can extract useful information from DWARF/PDB
debugging data. Its goal is to use the debugging information to provide
insights into the code generation. This can be used to guide improvements
to the code. Examples of questions it hopes to answer (but not all are
implemented yet):

* What is the memory layout of a struct?
* Which small functions aren't inlined?
* Which large functions are inlined many times?
* Which functions have bounds checks after optimization, or more generally,
which functions can panic?
* What difference does a source code change make to code generation?
* What difference does a compiler version change make to code generation?

**This is alpha software. It is likely to contain many bugs and
incomplete features.** Neverthless, it is in a state where it can still
provide some use. Bug reports and feature requests are welcome.

Supports:
* ELF files with DWARF
* Mach-O files with DWARF
* Windows PDB files (mimimal support so far)

## Installing
After installing [Rust](https://www.rust-lang.org/), run:
```
cargo install ddbug
```
or
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

## License
This software is licensed under either of

  * Apache License, Version 2.0 ([`LICENSE-APACHE`](./LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
  * MIT license ([`LICENSE-MIT`](./LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

This software links with a number of libraries, which
have their own licenses. In particular, it links with the
[panopticon](https://github.com/das-labor/panopticon) library, which is
licensed under GPL Version 3.
