use std::io::BufWriter;

const OPT_FILE: &str = "file";

// Print format
const OPT_OUTPUT: &str = "format";
const OPT_OUTPUT_TEXT: &str = "text";
const OPT_OUTPUT_HTML: &str = "html";

fn main() {
    env_logger::init();

    let mut cmd = clap::Command::new("ddbug")
        .version(clap::crate_version!())
        .arg(
            clap::Arg::new(OPT_FILE)
                .help("Path of file to print")
                .value_name("FILE")
                .index(1),
        )
        .arg(
            clap::Arg::new(OPT_OUTPUT)
                .short('o')
                .long(OPT_OUTPUT)
                .help("Output format")
                .takes_value(true)
                .value_name("FORMAT")
                .possible_values(&[OPT_OUTPUT_TEXT, OPT_OUTPUT_HTML]),
        );
    let matches = cmd.get_matches_mut();
    let mut options = ddbug::Options::default();
    options.inline_depth = 1;
    options.category_file = true;
    options.category_unit = true;
    options.category_type = true;
    options.category_function = true;
    options.category_variable = true;

    if let Some(value) = matches.value_of(OPT_OUTPUT) {
        match value {
            OPT_OUTPUT_TEXT => options.html = false,
            OPT_OUTPUT_HTML => options.html = true,
            _ => cmd
                .error(
                    clap::ErrorKind::InvalidValue,
                    format!("invalid {} value: {}", OPT_OUTPUT, value),
                )
                .exit(),
        }
    }

    let path = matches.value_of(OPT_FILE).unwrap();
    if let Err(e) = bloat(path.to_string(), &options) {
        log::error!("{}: {}", path, e);
    }
}

fn bloat(path: String, options: &ddbug::Options) -> ddbug::Result<()> {
    let file = ddbug::File::parse(path)?;
    ddbug::assign_ids(file.file(), options);
    let stdout = std::io::stdout();
    let mut writer = BufWriter::new(stdout.lock());
    if options.html {
        let mut printer = ddbug::HtmlPrinter::new(&mut writer, options);
        printer.begin()?;
        ddbug::bloat(file.file(), &mut printer, options)?;
        printer.end()?;
    } else {
        let mut printer = ddbug::TextPrinter::new(&mut writer, options);
        ddbug::bloat(file.file(), &mut printer, options)?;
    }
    Ok(())
}
