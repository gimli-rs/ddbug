extern crate env_logger;
extern crate getopts;
#[macro_use]
extern crate log;

use std::env;
use std::io::{self, Write};

extern crate ddbug;

fn main() {
    env_logger::init().ok();

    let mut opts = getopts::Options::new();
    opts.optflag("", "calls", "print subprogram calls");
    opts.optflag("", "diff", "print difference between two files");
    opts.optflag("", "sort", "sort entries by type and name");
    opts.optopt("",
                "inline-depth",
                "depth of inlined subroutine calls (0 to disable)",
                "DEPTH");
    opts.optopt("", "name", "print only members with the given name", "NAME");
    opts.optopt("",
                "namespace",
                "print only members of the given namespace",
                "NAMESPACE");

    let matches = match opts.parse(env::args().skip(1)) {
        Ok(m) => m,
        Err(e) => {
            error!("{}", e);
            print_usage(&opts);
        }
    };

    let calls = matches.opt_present("calls");
    let diff = matches.opt_present("diff");
    let sort = matches.opt_present("sort");
    let inline_depth = if let Some(inline_depth) = matches.opt_str("inline-depth") {
        match inline_depth.parse::<usize>() {
            Ok(inline_depth) => inline_depth,
            Err(e) => {
                error!("Invalid argument '{}' to option 'inline-depth': {}",
                       inline_depth,
                       e);
                print_usage(&opts);
            }
        }
    } else {
        1
    };
    let name = matches.opt_str("name");
    let name = name.as_ref().map(|s| &s[..]);
    let namespace = matches.opt_str("namespace");
    let namespace = match namespace {
        Some(ref namespace) => namespace.split("::").collect(),
        None => Vec::new(),
    };

    let flags = ddbug::Flags {
        calls: calls,
        sort: sort,
        inline_depth: inline_depth,
        name: name,
        namespace: namespace,
    };

    if diff {
        if matches.free.len() != 2 {
            error!("Invalid filename arguments (expected 2 filenames, found {})",
                   matches.free.len());
            print_usage(&opts);
        }
        let path_a = &matches.free[0];
        let path_b = &matches.free[1];

        if let Err(e) = ddbug::parse_file(path_a,
                                          &mut |file_a| {
            if let Err(e) = ddbug::parse_file(path_b,
                                              &mut |file_b| diff_file(file_a, file_b, &flags)) {
                error!("{}: {}", path_b, e);
            }
            Ok(())
        }) {
            error!("{}: {}", path_a, e);
        }
    } else {
        if matches.free.len() != 1 {
            error!("Invalid filename arguments (expected 1 filename, found {})",
                   matches.free.len());
            print_usage(&opts);
        }
        let path = &matches.free[0];

        if let Err(e) = ddbug::parse_file(path, &mut |file| print_file(file, &flags)) {
            error!("{}: {}", path, e);
        }
    }
}

fn diff_file(
    file_a: &mut ddbug::File,
    file_b: &mut ddbug::File,
    flags: &ddbug::Flags
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
    ddbug::print_file(&mut writer, file, &flags)
}

fn print_usage(opts: &getopts::Options) -> ! {
    let brief = format!("Usage: {} <options> <file>", env::args().next().unwrap());
    write!(&mut io::stderr(), "{}", opts.usage(&brief)).ok();
    std::process::exit(1);
}
