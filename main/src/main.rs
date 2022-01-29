// Enable some rust 2018 idioms.
#![warn(bare_trait_objects)]
#![warn(unused_extern_crates)]

#[cfg(feature = "system_alloc")]
use std::alloc::System;

#[cfg(feature = "system_alloc")]
#[global_allocator]
static A: System = System;

#[macro_use]
extern crate clap;
#[macro_use]
extern crate log;

use std::io::BufWriter;

use warp::Filter;

// Mode
const OPT_FILE: &str = "file";
const OPT_DIFF: &str = "diff";

// Print format
const OPT_OUTPUT: &str = "format";
const OPT_OUTPUT_TEXT: &str = "text";
const OPT_OUTPUT_HTML: &str = "html";
const OPT_OUTPUT_HTTP: &str = "http";

// Print categories
const OPT_CATEGORY: &str = "category";
const OPT_CATEGORY_FILE: &str = "file";
const OPT_CATEGORY_UNIT: &str = "unit";
const OPT_CATEGORY_TYPE: &str = "type";
const OPT_CATEGORY_FUNCTION: &str = "function";
const OPT_CATEGORY_VARIABLE: &str = "variable";

// Print fields
const OPT_PRINT: &str = "print";
const OPT_PRINT_ALL: &str = "all";
const OPT_PRINT_ADDRESS: &str = "address";
const OPT_PRINT_SOURCE: &str = "source";
const OPT_PRINT_FILE_ADDRESS: &str = "file-address";
const OPT_PRINT_UNIT_ADDRESS: &str = "unit-address";
const OPT_PRINT_FUNCTION_CALLS: &str = "function-calls";
const OPT_PRINT_FUNCTION_INSTRUCTIONS: &str = "function-instructions";
const OPT_PRINT_FUNCTION_VARIABLES: &str = "function-variables";
const OPT_PRINT_FUNCTION_STACK_FRAME: &str = "function-stack-frame";
const OPT_PRINT_INLINED_FUNCTION_PARAMETERS: &str = "inlined-function-parameters";
const OPT_PRINT_VARIABLE_LOCATIONS: &str = "variable-locations";

// Print parameters
const OPT_INLINE_DEPTH: &str = "inline-depth";

// Filters
const OPT_FILTER: &str = "filter";
const OPT_FILTER_INLINE: &str = "inline";
const OPT_FILTER_FUNCTION_INLINE: &str = "function-inline";
const OPT_FILTER_NAME: &str = "name";
const OPT_FILTER_NAMESPACE: &str = "namespace";
const OPT_FILTER_UNIT: &str = "unit";

// Sorting
const OPT_SORT: &str = "sort";
const OPT_SORT_SIZE: &str = "size";
const OPT_SORT_NAME: &str = "name";

// Diff options
const OPT_IGNORE: &str = "ignore";
const OPT_IGNORE_ADDED: &str = "added";
const OPT_IGNORE_DELETED: &str = "deleted";
const OPT_IGNORE_ADDRESS: &str = "address";
const OPT_IGNORE_LINKAGE_NAME: &str = "linkage-name";
const OPT_IGNORE_SYMBOL_NAME: &str = "symbol-name";
const OPT_IGNORE_FUNCTION_ADDRESS: &str = "function-address";
const OPT_IGNORE_FUNCTION_SIZE: &str = "function-size";
const OPT_IGNORE_FUNCTION_INLINE: &str = "function-inline";
const OPT_IGNORE_FUNCTION_SYMBOL_NAME: &str = "function-symbol-name";
const OPT_IGNORE_VARIABLE_ADDRESS: &str = "variable-address";
const OPT_IGNORE_VARIABLE_SYMBOL_NAME: &str = "variable-symbol-name";
const OPT_PREFIX_MAP: &str = "prefix-map";

fn main() {
    env_logger::init();

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
                .short("d")
                .long(OPT_DIFF)
                .help("Print difference between two files")
                .value_names(&["FILE", "FILE"]),
        )
        .arg(
            clap::Arg::with_name(OPT_OUTPUT)
                .short("o")
                .long(OPT_OUTPUT)
                .help("Output format")
                .takes_value(true)
                .value_name("FORMAT")
                .possible_values(&[OPT_OUTPUT_TEXT, OPT_OUTPUT_HTML, OPT_OUTPUT_HTTP]),
        )
        .arg(
            clap::Arg::with_name(OPT_CATEGORY)
                .short("c")
                .long(OPT_CATEGORY)
                .help("Categories of entries to print (defaults to all)")
                .takes_value(true)
                .multiple(true)
                .require_delimiter(true)
                .value_name("CATEGORY")
                .possible_values(&[
                    OPT_CATEGORY_FILE,
                    OPT_CATEGORY_UNIT,
                    OPT_CATEGORY_TYPE,
                    OPT_CATEGORY_FUNCTION,
                    OPT_CATEGORY_VARIABLE,
                ]),
        )
        .arg(
            clap::Arg::with_name(OPT_PRINT)
                .short("p")
                .long(OPT_PRINT)
                .help("Print extra fields within entries")
                .takes_value(true)
                .multiple(true)
                .require_delimiter(true)
                .value_name("FIELD")
                .possible_values(&[
                    OPT_PRINT_ALL,
                    OPT_PRINT_ADDRESS,
                    OPT_PRINT_SOURCE,
                    OPT_PRINT_FILE_ADDRESS,
                    OPT_PRINT_UNIT_ADDRESS,
                    OPT_PRINT_FUNCTION_CALLS,
                    OPT_PRINT_FUNCTION_INSTRUCTIONS,
                    OPT_PRINT_FUNCTION_VARIABLES,
                    OPT_PRINT_FUNCTION_STACK_FRAME,
                    OPT_PRINT_INLINED_FUNCTION_PARAMETERS,
                    OPT_PRINT_VARIABLE_LOCATIONS,
                ]),
        )
        .arg(
            clap::Arg::with_name(OPT_INLINE_DEPTH)
                .long(OPT_INLINE_DEPTH)
                .help("Depth of inlined function calls to print (defaults to 1, 0 to disable)")
                .value_name("DEPTH"),
        )
        .arg(
            clap::Arg::with_name(OPT_FILTER)
                .short("f")
                .long(OPT_FILTER)
                .help("Print only entries that match the given filters")
                .takes_value(true)
                .multiple(true)
                .require_delimiter(true)
                .value_name("FILTER"),
        )
        .arg(
            clap::Arg::with_name(OPT_SORT)
                .short("s")
                .long(OPT_SORT)
                .help("Sort entries by the given key")
                .takes_value(true)
                .value_name("KEY")
                .possible_values(&[OPT_SORT_NAME, OPT_SORT_SIZE]),
        )
        .arg(
            clap::Arg::with_name(OPT_IGNORE)
                .short("i")
                .long(OPT_IGNORE)
                .help("Don't print differences due to the given types of changes")
                .requires(OPT_DIFF)
                .takes_value(true)
                .multiple(true)
                .require_delimiter(true)
                .value_name("CHANGE")
                .possible_values(&[
                    OPT_IGNORE_ADDED,
                    OPT_IGNORE_DELETED,
                    OPT_IGNORE_ADDRESS,
                    OPT_IGNORE_LINKAGE_NAME,
                    OPT_IGNORE_SYMBOL_NAME,
                    OPT_IGNORE_FUNCTION_ADDRESS,
                    OPT_IGNORE_FUNCTION_SIZE,
                    OPT_IGNORE_FUNCTION_INLINE,
                    OPT_IGNORE_FUNCTION_SYMBOL_NAME,
                    OPT_IGNORE_VARIABLE_ADDRESS,
                    OPT_IGNORE_VARIABLE_SYMBOL_NAME,
                ]),
        )
        .arg(
            clap::Arg::with_name(OPT_PREFIX_MAP)
                .long(OPT_PREFIX_MAP)
                .help("When comparing file paths, replace the 'old' prefix with the 'new' prefix")
                .requires(OPT_DIFF)
                .takes_value(true)
                .multiple(true)
                .require_delimiter(true)
                .value_name("OLD>=<NEW"),
        )
        .after_help(concat!(
            "FILTERS:\n",
            "    function-inline=<yes|no>        Match function 'inline' value\n",
            "    name=<string>                   Match entries with the given name\n",
            "    namespace=<string>              Match entries within the given namespace\n",
            "    unit=<string>                   Match entries within the given unit\n"
        ))
        .get_matches();

    let mut options = ddbug::Options::default();

    if let Some(value) = matches.value_of(OPT_OUTPUT) {
        match value {
            OPT_OUTPUT_TEXT => options.html = false,
            OPT_OUTPUT_HTML => options.html = true,
            OPT_OUTPUT_HTTP => {
                options.html = true;
                options.http = true;
            }
            _ => clap::Error::with_description(
                &format!("invalid {} value: {}", OPT_OUTPUT, value),
                clap::ErrorKind::InvalidValue,
            )
            .exit(),
        }
    } else {
        options.html = false;
    }

    options.inline_depth = if let Some(inline_depth) = matches.value_of(OPT_INLINE_DEPTH) {
        match inline_depth.parse::<usize>() {
            Ok(inline_depth) => inline_depth,
            Err(_) => {
                clap::Error::with_description(
                    &format!("invalid {} value: {}", OPT_INLINE_DEPTH, inline_depth),
                    clap::ErrorKind::InvalidValue,
                )
                .exit();
            }
        }
    } else {
        1
    };

    if let Some(values) = matches.values_of(OPT_CATEGORY) {
        for value in values {
            match value {
                OPT_CATEGORY_FILE => options.category_file = true,
                OPT_CATEGORY_UNIT => options.category_unit = true,
                OPT_CATEGORY_TYPE => options.category_type = true,
                OPT_CATEGORY_FUNCTION => options.category_function = true,
                OPT_CATEGORY_VARIABLE => options.category_variable = true,
                _ => clap::Error::with_description(
                    &format!("invalid {} value: {}", OPT_CATEGORY, value),
                    clap::ErrorKind::InvalidValue,
                )
                .exit(),
            }
        }
    } else {
        options.category_file = true;
        options.category_unit = true;
        options.category_type = true;
        options.category_function = true;
        options.category_variable = true;
    }

    if let Some(values) = matches.values_of(OPT_PRINT) {
        for value in values {
            match value {
                OPT_PRINT_ALL => {
                    options.print_file_address = true;
                    options.print_unit_address = true;
                    options.print_source = true;
                    options.print_function_calls = true;
                    options.print_function_instructions = true;
                    options.print_function_variables = true;
                    options.print_function_stack_frame = true;
                    options.print_inlined_function_parameters = true;
                    options.print_variable_locations = true;
                }
                OPT_PRINT_ADDRESS => {
                    options.print_file_address = true;
                    options.print_unit_address = true;
                }
                OPT_PRINT_SOURCE => options.print_source = true,
                OPT_PRINT_FILE_ADDRESS => options.print_file_address = true,
                OPT_PRINT_UNIT_ADDRESS => options.print_unit_address = true,
                OPT_PRINT_FUNCTION_CALLS => options.print_function_calls = true,
                OPT_PRINT_FUNCTION_INSTRUCTIONS => options.print_function_instructions = true,
                OPT_PRINT_FUNCTION_VARIABLES => options.print_function_variables = true,
                OPT_PRINT_FUNCTION_STACK_FRAME => options.print_function_stack_frame = true,
                OPT_PRINT_INLINED_FUNCTION_PARAMETERS => {
                    options.print_inlined_function_parameters = true
                }
                OPT_PRINT_VARIABLE_LOCATIONS => options.print_variable_locations = true,
                _ => clap::Error::with_description(
                    &format!("invalid {} value: {}", OPT_PRINT, value),
                    clap::ErrorKind::InvalidValue,
                )
                .exit(),
            }
        }
    }

    if let Some(values) = matches.values_of(OPT_FILTER) {
        for value in values {
            if let Some(index) = value.bytes().position(|c| c == b'=') {
                let key = &value[..index];
                let value = &value[index + 1..];
                match key {
                    OPT_FILTER_INLINE | OPT_FILTER_FUNCTION_INLINE => {
                        options.filter_function_inline = match value {
                            "y" | "yes" => Some(true),
                            "n" | "no" => Some(false),
                            _ => clap::Error::with_description(
                                &format!("invalid {} {} value: {}", OPT_FILTER, key, value),
                                clap::ErrorKind::InvalidValue,
                            )
                            .exit(),
                        };
                    }
                    OPT_FILTER_NAME => options.filter_name = Some(value.into()),
                    OPT_FILTER_NAMESPACE => {
                        options.filter_namespace = value.split("::").map(String::from).collect()
                    }
                    OPT_FILTER_UNIT => options.filter_unit = Some(value.into()),
                    _ => clap::Error::with_description(
                        &format!("invalid {} key: {}", OPT_FILTER, key),
                        clap::ErrorKind::InvalidValue,
                    )
                    .exit(),
                }
            } else {
                clap::Error::with_description(
                    &format!("missing {} value for key: {}", OPT_FILTER, value),
                    clap::ErrorKind::InvalidValue,
                )
                .exit();
            }
        }
    }

    options.sort = match matches.value_of(OPT_SORT) {
        Some(OPT_SORT_NAME) => ddbug::Sort::Name,
        Some(OPT_SORT_SIZE) => ddbug::Sort::Size,
        Some(value) => clap::Error::with_description(
            &format!("invalid {} key: {}", OPT_SORT, value),
            clap::ErrorKind::InvalidValue,
        )
        .exit(),
        _ => ddbug::Sort::None,
    };

    if let Some(values) = matches.values_of(OPT_IGNORE) {
        for value in values {
            match value {
                OPT_IGNORE_ADDED => options.ignore_added = true,
                OPT_IGNORE_DELETED => options.ignore_deleted = true,
                OPT_IGNORE_ADDRESS => {
                    options.ignore_function_address = true;
                    options.ignore_variable_address = true;
                }
                OPT_IGNORE_LINKAGE_NAME => {
                    options.ignore_function_linkage_name = true;
                    options.ignore_variable_linkage_name = true;
                }
                OPT_IGNORE_SYMBOL_NAME => {
                    options.ignore_function_symbol_name = true;
                    options.ignore_variable_symbol_name = true;
                }
                OPT_IGNORE_FUNCTION_ADDRESS => options.ignore_function_address = true,
                OPT_IGNORE_FUNCTION_SIZE => options.ignore_function_size = true,
                OPT_IGNORE_FUNCTION_INLINE => options.ignore_function_inline = true,
                OPT_IGNORE_FUNCTION_SYMBOL_NAME => options.ignore_function_symbol_name = true,
                OPT_IGNORE_VARIABLE_ADDRESS => options.ignore_variable_address = true,
                OPT_IGNORE_VARIABLE_SYMBOL_NAME => options.ignore_variable_symbol_name = true,
                _ => clap::Error::with_description(
                    &format!("invalid {} value: {}", OPT_IGNORE, value),
                    clap::ErrorKind::InvalidValue,
                )
                .exit(),
            }
        }
    }

    if let Some(values) = matches.values_of(OPT_PREFIX_MAP) {
        for value in values {
            if let Some(index) = value.bytes().position(|c| c == b'=') {
                let old = &value[..index];
                let new = &value[index + 1..];
                options.prefix_map.push((old.into(), new.into()));
            } else {
                clap::Error::with_description(
                    &format!("invalid {} value: {}", OPT_PREFIX_MAP, value),
                    clap::ErrorKind::InvalidValue,
                )
                .exit();
            }
        }
        options.prefix_map.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
    }

    if let Some(mut paths) = matches.values_of(OPT_DIFF) {
        let path_a = paths.next().unwrap();
        let path_b = paths.next().unwrap();

        match ddbug::File::parse(path_a.to_string()) {
            Err(e) => error!("{}: {}", path_a, e),
            Ok(file_a) => match ddbug::File::parse(path_b.to_string()) {
                Err(e) => error!("{}: {}", path_b, e),
                Ok(file_b) => {
                    if let Err(e) = {
                        let ids = ddbug::assign_merged_ids(file_a.file(), file_b.file(), &options);
                        if options.http {
                            serve_diff_file(file_a, file_b, options, ids)
                        } else {
                            diff_file(file_a.file(), file_b.file(), &options)
                        }
                    } {
                        error!("{}", e);
                    }
                }
            },
        }
    } else {
        let path = matches.value_of(OPT_FILE).unwrap();

        if let Err(e) = ddbug::File::parse(path.to_string()).and_then(|file| {
            let ids = ddbug::assign_ids(file.file(), &options);
            if options.http {
                serve_print_file(file, options, ids)
            } else {
                print_file(file.file(), &options)
            }
        }) {
            error!("{}: {}", path, e);
        }
    }
}

fn diff_file(
    file_a: &ddbug::File,
    file_b: &ddbug::File,
    options: &ddbug::Options,
) -> ddbug::Result<()> {
    format(options, |printer| {
        if let Err(e) = ddbug::diff(printer, file_a, file_b, options) {
            error!("{}", e);
        }
        Ok(())
    })
}

fn print_file(file: &ddbug::File, options: &ddbug::Options) -> ddbug::Result<()> {
    format(options, |printer| ddbug::print(file, printer, options))
}

fn format<F>(options: &ddbug::Options, f: F) -> ddbug::Result<()>
where
    F: FnOnce(&mut dyn ddbug::Printer) -> ddbug::Result<()>,
{
    let stdout = std::io::stdout();
    let mut writer = BufWriter::new(stdout.lock());
    if options.html {
        let mut printer = ddbug::HtmlPrinter::new(&mut writer, options);
        printer.begin()?;
        f(&mut printer)?;
        printer.end()
    } else {
        let mut printer = ddbug::TextPrinter::new(&mut writer, options);
        f(&mut printer)
    }
}

fn serve_diff_file(
    file_a: parser::FileContext,
    file_b: parser::FileContext,
    options: ddbug::Options,
    ids: Vec<(ddbug::Id, ddbug::Id)>,
) -> ddbug::Result<()> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_io()
        .build()
        .unwrap();
    rt.block_on(async move {
        let file_a = std::sync::Arc::new(file_a);
        let file_b = std::sync::Arc::new(file_b);
        let options = std::sync::Arc::new(options);
        let ids = std::sync::Arc::new(ids);

        let route_root = {
            let file_a = file_a.clone();
            let file_b = file_b.clone();
            let options = options.clone();
            warp::path::end().map(move || {
                let mut writer = Vec::new();
                let mut printer = ddbug::HtmlPrinter::new(&mut writer, &options);
                printer.begin().unwrap();
                ddbug::diff(&mut printer, file_a.file(), file_b.file(), &options).unwrap();
                printer.end().unwrap();
                warp::reply::html(writer)
            })
        };
        let route_id = {
            warp::path!("id" / usize).map(move |id| {
                let mut writer = Vec::new();
                if let Some(id) = ids.get(id) {
                    let mut printer = ddbug::HtmlPrinter::new(&mut writer, &options);
                    ddbug::diff_id(*id, file_a.file(), file_b.file(), &mut printer, &options)
                        .unwrap();
                }
                writer
            })
        };
        let route = warp::get().and(route_root.or(route_id));

        let (addr, serve) = warp::serve(route).bind_ephemeral(([127, 0, 0, 1], 0));
        println!("Listening on http://{}", addr);
        // TODO: support other OS
        #[cfg(target_os = "linux")]
        std::process::Command::new("xdg-open")
            .arg(format!("http://{}", addr))
            .status()
            .unwrap();
        serve.await;
    });

    Ok(())
}

fn serve_print_file(
    file: parser::FileContext,
    options: ddbug::Options,
    ids: Vec<ddbug::Id>,
) -> ddbug::Result<()> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_io()
        .build()
        .unwrap();
    rt.block_on(async move {
        let file = std::sync::Arc::new(file);
        let options = std::sync::Arc::new(options);
        let ids = std::sync::Arc::new(ids);

        let route_root = {
            let file = file.clone();
            let options = options.clone();
            warp::path::end().map(move || {
                let mut writer = Vec::new();
                let mut printer = ddbug::HtmlPrinter::new(&mut writer, &options);
                printer.begin().unwrap();
                ddbug::print(file.file(), &mut printer, &options).unwrap();
                printer.end().unwrap();
                warp::reply::html(writer)
            })
        };
        let route_id = {
            warp::path!("id" / usize).map(move |id| {
                let mut writer = Vec::new();
                if let Some(id) = ids.get(id) {
                    let mut printer = ddbug::HtmlPrinter::new(&mut writer, &options);
                    ddbug::print_id(*id, file.file(), &mut printer, &options).unwrap();
                }
                writer
            })
        };
        let route = warp::get().and(route_root.or(route_id));

        let (addr, serve) = warp::serve(route).bind_ephemeral(([127, 0, 0, 1], 0));
        println!("Listening on http://{}", addr);
        // TODO: support other OS
        #[cfg(target_os = "linux")]
        std::process::Command::new("xdg-open")
            .arg(format!("http://{}", addr))
            .status()
            .unwrap();
        serve.await;
    });

    Ok(())
}

mod www {}
