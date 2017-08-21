#[macro_use]
extern crate clap;
extern crate env_logger;
#[macro_use]
extern crate log;

use std::io::{self, Write};

extern crate ddbug;

fn main() {
    env_logger::init().ok();

    let matches = clap::App::new("ddbug")
        .version(crate_version!())
        .arg(
            clap::Arg::with_name("file")
                .help("path of file to print")
                .value_name("FILE")
                .index(1)
                .required_unless("diff")
                .conflicts_with("diff"),
        )
        .arg(
            clap::Arg::with_name("diff")
                .long("diff")
                .help("print difference between two files")
                .value_names(&["FILE", "FILE"]),
        )
        .arg(clap::Arg::with_name("calls").long("calls").help("print function calls"))
        .arg(
            clap::Arg::with_name("sort-name")
                .long("sort-name")
                .help("sort entries by type and name"),
        )
        .arg(clap::Arg::with_name("sort-size").long("sort-size").help("sort entries by size"))
        .arg(
            clap::Arg::with_name("ignore-added")
                .long("ignore-added")
                .help("don't display differences due to added functions/types/variables"),
        )
        .arg(
            clap::Arg::with_name("ignore-deleted")
                .long("ignore-deleted")
                .help("don't display differences due to deleted functions/types/variables"),
        )
        .arg(
            clap::Arg::with_name("ignore-function-address")
                .long("ignore-function-address")
                .help("don't display function differences due to address changes"),
        )
        .arg(
            clap::Arg::with_name("ignore-function-size")
                .long("ignore-function-size")
                .help("don't display function differences due to size changes"),
        )
        .arg(
            clap::Arg::with_name("ignore-function-inline")
                .long("ignore-function-inline")
                .help("don't display function differences due to inline changes"),
        )
        .arg(
            clap::Arg::with_name("ignore-variable-address")
                .long("ignore-variable-address")
                .help("don't display variable differences due to address changes"),
        )
        .arg(
            clap::Arg::with_name("inline-depth")
                .long("inline-depth")
                .help("depth of inlined function calls (0 to disable)")
                .value_name("DEPTH"),
        )
        .arg(
            clap::Arg::with_name("unit")
                .long("unit")
                .help("print only entries within the given unit")
                .value_name("UNIT"),
        )
        .arg(
            clap::Arg::with_name("name")
                .long("name")
                .help("print only entries with the given name")
                .value_name("NAME"),
        )
        .arg(
            clap::Arg::with_name("namespace")
                .long("namespace")
                .help("print only entries within the given namespace")
                .value_name("NAMESPACE"),
        )
        .arg(clap::Arg::with_name("filter-unit").long("filter-unit").help("print only units"))
        .arg(clap::Arg::with_name("filter-type").long("filter-type").help("print only types"))
        .arg(
            clap::Arg::with_name("filter-function")
                .long("filter-function")
                .help("print only functions"),
        )
        .arg(
            clap::Arg::with_name("filter-variable")
                .long("filter-variable")
                .help("print only variables"),
        )
        .get_matches();

    let calls = matches.is_present("calls");
    let sort = if matches.is_present("sort-name") {
        ddbug::Sort::Name
    } else if matches.is_present("sort-size") {
        ddbug::Sort::Size
    } else {
        ddbug::Sort::None
    };
    let ignore_added = matches.is_present("ignore-added");
    let ignore_deleted = matches.is_present("ignore-deleted");
    let ignore_function_address = matches.is_present("ignore-function-address");
    let ignore_function_size = matches.is_present("ignore-function-size");
    let ignore_function_inline = matches.is_present("ignore-function-inline");
    let ignore_variable_address = matches.is_present("ignore-variable-address");
    let inline_depth = if let Some(inline_depth) = matches.value_of("inline-depth") {
        match inline_depth.parse::<usize>() {
            Ok(inline_depth) => inline_depth,
            Err(e) => {
                error!("Invalid argument '{}' to option 'inline-depth': {}", inline_depth, e);
                print_usage(&matches);
            }
        }
    } else {
        1
    };
    let unit = matches.value_of("unit");
    let unit = unit.as_ref().map(|s| &s[..]);
    let name = matches.value_of("name");
    let name = name.as_ref().map(|s| &s[..]);
    let namespace = matches.value_of("namespace");
    let namespace = match namespace {
        Some(ref namespace) => namespace.split("::").collect(),
        None => Vec::new(),
    };
    let mut filter_unit = matches.is_present("filter-unit");
    let mut filter_type = matches.is_present("filter-type");
    let mut filter_function = matches.is_present("filter-function");
    let mut filter_variable = matches.is_present("filter-variable");
    if !filter_unit && !filter_type && !filter_function && !filter_variable {
        if name.is_none() {
            filter_unit = true;
        }
        filter_type = true;
        filter_function = true;
        filter_variable = true;
    }

    let flags = ddbug::Flags {
        calls,
        sort,
        ignore_added,
        ignore_deleted: ignore_deleted,
        ignore_function_address,
        ignore_function_size,
        ignore_function_inline,
        ignore_variable_address,
        inline_depth,
        unit,
        name,
        namespace,
        filter_unit,
        filter_type,
        filter_function,
        filter_variable,
    };

    if let Some(mut paths) = matches.values_of("diff") {
        let path_a = paths.next().unwrap();
        let path_b = paths.next().unwrap();

        if let Err(e) = ddbug::parse_file(path_a, &mut |file_a| {
            if let Err(e) =
                ddbug::parse_file(path_b, &mut |file_b| diff_file(file_a, file_b, &flags))
            {
                error!("{}: {}", path_b, e);
            }
            Ok(())
        }) {
            error!("{}: {}", path_a, e);
        }
    } else {
        let path = matches.value_of("file").unwrap();

        if let Err(e) = ddbug::parse_file(path, &mut |file| print_file(file, &flags)) {
            error!("{}: {}", path, e);
        }
    }
}

fn diff_file(
    file_a: &mut ddbug::File,
    file_b: &mut ddbug::File,
    flags: &ddbug::Flags,
) -> ddbug::Result<()> {
    let stdout = std::io::stdout();
    let mut writer = stdout.lock();
    if let Err(e) = ddbug::diff_file(&mut writer, file_a, file_b, flags) {
        error!("{}", e);
    }
    Ok(())
}

fn print_file(file: &mut ddbug::File, flags: &ddbug::Flags) -> ddbug::Result<()> {
    let stdout = std::io::stdout();
    let mut writer = stdout.lock();
    ddbug::print_file(&mut writer, file, flags)
}

fn print_usage(matches: &clap::ArgMatches) -> ! {
    write!(&mut io::stderr(), "{}", matches.usage()).ok();
    std::process::exit(1);
}
