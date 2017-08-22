#[macro_use]
extern crate clap;
extern crate env_logger;
#[macro_use]
extern crate log;

use std::io::{self, Write};

extern crate ddbug;

// Mode
const OPT_FILE: &'static str = "file";
const OPT_DIFF: &'static str = "diff";

// Display options
const OPT_CALLS: &'static str = "calls";
const OPT_INLINE_DEPTH: &'static str = "inline-depth";

// Display categories
const OPT_CATEGORY: &'static str = "category";
const OPT_CATEGORY_UNIT: &'static str = "unit";
const OPT_CATEGORY_TYPE: &'static str = "type";
const OPT_CATEGORY_FUNCTION: &'static str = "function";
const OPT_CATEGORY_VARIABLE: &'static str = "variable";

// Filters
const OPT_UNIT: &'static str = "unit";
const OPT_NAME: &'static str = "name";
const OPT_NAMESPACE: &'static str = "namespace";

// Sorting
const OPT_SORT: &'static str = "sort";
const OPT_SORT_SIZE: &'static str = "size";
const OPT_SORT_NAME: &'static str = "name";

// Diff options
const OPT_IGNORE: &'static str = "ignore";
const OPT_IGNORE_ADDED: &'static str = "added";
const OPT_IGNORE_DELETED: &'static str = "deleted";
const OPT_IGNORE_FUNCTION_ADDRESS: &'static str = "function-address";
const OPT_IGNORE_FUNCTION_SIZE: &'static str = "function-size";
const OPT_IGNORE_FUNCTION_INLINE: &'static str = "function-inline";
const OPT_IGNORE_VARIABLE_ADDRESS: &'static str = "variable-address";

fn main() {
    env_logger::init().ok();

    let matches = clap::App::new("ddbug")
        .version(crate_version!())
        .setting(clap::AppSettings::UnifiedHelpMessage)
        .arg(
            clap::Arg::with_name(OPT_FILE)
                .help("Path of file to print")
                .value_name("FILE")
                .index(1)
                .required_unless(OPT_DIFF)
                .conflicts_with(OPT_DIFF),
        )
        .arg(
            clap::Arg::with_name(OPT_DIFF)
                .long("diff")
                .help("Print difference between two files")
                .value_names(&["FILE", "FILE"]),
        )
        .arg(clap::Arg::with_name(OPT_CALLS).long("calls").help("Print function calls"))
        .arg(
            clap::Arg::with_name(OPT_INLINE_DEPTH)
                .long("inline-depth")
                .help("Depth of inlined function calls (defaults to 1, 0 to disable)")
                .value_name("DEPTH"),
        )
        .arg(
            clap::Arg::with_name(OPT_CATEGORY)
                .long("category")
                .help("Categories of entries to display (defaults to all)")
                .takes_value(true)
                .multiple(true)
                .require_delimiter(true)
                .value_name("CATEGORY")
                .possible_values(&[
                    OPT_CATEGORY_UNIT,
                    OPT_CATEGORY_TYPE,
                    OPT_CATEGORY_FUNCTION,
                    OPT_CATEGORY_VARIABLE,
                ]),
        )
        .arg(
            clap::Arg::with_name(OPT_UNIT)
                .long("unit")
                .help("Print only entries within the given unit")
                .value_name("UNIT"),
        )
        .arg(
            clap::Arg::with_name(OPT_NAME)
                .long("name")
                .help("Print only entries with the given name")
                .value_name("NAME"),
        )
        .arg(
            clap::Arg::with_name(OPT_NAMESPACE)
                .long("namespace")
                .help("Print only entries within the given namespace")
                .value_name("NAMESPACE"),
        )
        .arg(
            clap::Arg::with_name(OPT_SORT)
                .long("sort")
                .help("Sort entries by the given key")
                .takes_value(true)
                .value_name("KEY")
                .possible_values(&[OPT_SORT_NAME, OPT_SORT_SIZE]),
        )
        .arg(
            clap::Arg::with_name(OPT_IGNORE)
                .long("ignore")
                .help("Don't display differences due to the given types of changes")
                .requires(OPT_DIFF)
                .takes_value(true)
                .multiple(true)
                .require_delimiter(true)
                .value_name("CHANGE")
                .possible_values(&[
                    OPT_IGNORE_ADDED,
                    OPT_IGNORE_DELETED,
                    OPT_IGNORE_FUNCTION_ADDRESS,
                    OPT_IGNORE_FUNCTION_SIZE,
                    OPT_IGNORE_FUNCTION_INLINE,
                    OPT_IGNORE_VARIABLE_ADDRESS,
                ]),
        )
        .get_matches();

    let mut options = ddbug::Options::default();

    options.calls = matches.is_present(OPT_CALLS);

    options.inline_depth = if let Some(inline_depth) = matches.value_of(OPT_INLINE_DEPTH) {
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

    if let Some(values) = matches.values_of(OPT_CATEGORY) {
        for value in values {
            match value {
                OPT_CATEGORY_UNIT => options.category_unit = true,
                OPT_CATEGORY_TYPE => options.category_type = true,
                OPT_CATEGORY_FUNCTION => options.category_function = true,
                OPT_CATEGORY_VARIABLE => options.category_variable = true,
                _ => panic!("unrecognized category value: {}", value),
            }
        }
    } else {
        options.category_unit = true;
        options.category_type = true;
        options.category_function = true;
        options.category_variable = true;
    }

    options.unit = matches.value_of(OPT_UNIT);
    options.name = matches.value_of(OPT_NAME);
    options.namespace = match matches.value_of(OPT_NAMESPACE) {
        Some(ref namespace) => namespace.split("::").collect(),
        None => Vec::new(),
    };

    options.sort = match matches.value_of(OPT_SORT) {
        Some(OPT_SORT_NAME) => ddbug::Sort::Name,
        Some(OPT_SORT_SIZE) => ddbug::Sort::Size,
        Some(value) => panic!("unrecognized sort value: {}", value),
        _ => ddbug::Sort::None,
    };

    if let Some(values) = matches.values_of(OPT_IGNORE) {
        for value in values {
            match value {
                OPT_IGNORE_ADDED => options.ignore_added = true,
                OPT_IGNORE_DELETED => options.ignore_deleted = true,
                OPT_IGNORE_FUNCTION_ADDRESS => options.ignore_function_address = true,
                OPT_IGNORE_FUNCTION_SIZE => options.ignore_function_size = true,
                OPT_IGNORE_FUNCTION_INLINE => options.ignore_function_inline = true,
                OPT_IGNORE_VARIABLE_ADDRESS => options.ignore_variable_address = true,
                _ => panic!("unrecognized ignore value: {}", value),
            }
        }
    }

    if let Some(mut paths) = matches.values_of(OPT_DIFF) {
        let path_a = paths.next().unwrap();
        let path_b = paths.next().unwrap();

        if let Err(e) = ddbug::parse_file(path_a, &mut |file_a| {
            if let Err(e) =
                ddbug::parse_file(path_b, &mut |file_b| diff_file(file_a, file_b, &options))
            {
                error!("{}: {}", path_b, e);
            }
            Ok(())
        }) {
            error!("{}: {}", path_a, e);
        }
    } else {
        let path = matches.value_of(OPT_FILE).unwrap();

        if let Err(e) = ddbug::parse_file(path, &mut |file| print_file(file, &options)) {
            error!("{}: {}", path, e);
        }
    }
}

fn diff_file(
    file_a: &mut ddbug::File,
    file_b: &mut ddbug::File,
    options: &ddbug::Options,
) -> ddbug::Result<()> {
    let stdout = std::io::stdout();
    let mut writer = stdout.lock();
    if let Err(e) = ddbug::diff_file(&mut writer, file_a, file_b, options) {
        error!("{}", e);
    }
    Ok(())
}

fn print_file(file: &mut ddbug::File, options: &ddbug::Options) -> ddbug::Result<()> {
    let stdout = std::io::stdout();
    let mut writer = stdout.lock();
    ddbug::print_file(&mut writer, file, options)
}

fn print_usage(matches: &clap::ArgMatches) -> ! {
    write!(&mut io::stderr(), "{}", matches.usage()).ok();
    std::process::exit(1);
}
