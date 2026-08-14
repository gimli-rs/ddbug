struct Fixture {
    unit: &'static str,
    file1: &'static str,
    file2: &'static str,
}

fn print(fixture: &Fixture, name: &str, expect: &str) {
    let file = ddbug::File::parse(fixture.file1.into()).unwrap();
    let mut options = options();
    options.unit(fixture.unit).name(name);
    let mut output = Vec::new();
    let mut printer = ddbug::TextPrinter::new(&mut output, &options);
    ddbug::print(file.file(), &mut printer, &options).unwrap();
    let output = String::from_utf8(output).unwrap();
    if !equal(&output, expect) {
        println!("\nOutput:");
        println!("{output}");
        println!("Expected:");
        println!("{expect}");
        assert_eq!(output, expect);
    }
}

fn diff(fixture: &Fixture, name: &str, expect: &str) {
    let file1 = ddbug::File::parse(fixture.file1.into()).unwrap();
    let file2 = ddbug::File::parse(fixture.file2.into()).unwrap();
    let mut options = options();
    options.unit(fixture.unit).name(name);
    let mut diff = Vec::new();
    let mut printer = ddbug::TextPrinter::new(&mut diff, &options);
    ddbug::diff(&mut printer, file1.file(), file2.file(), &options).unwrap();
    let diff = String::from_utf8(diff).unwrap();
    if !equal(&diff, expect) {
        println!("\nDiff:");
        println!("{diff}");
        println!("Expected:");
        println!("{expect}");
        assert_eq!(diff, expect);
    }
}

fn options() -> ddbug::Options {
    ddbug::Options {
        print_function_variables: true,
        print_variable_locations: true,
        inline_depth: 1,

        category_unit: false,
        category_type: true,
        category_function: true,
        category_variable: true,

        filter_name: None,
        filter_namespace: Vec::new(),
        filter_unit: None,

        sort: ddbug::Sort::None,

        ignore_function_address: true,
        ignore_variable_address: true,
        ..Default::default()
    }
}

fn equal(mut output: &str, expect: &str) -> bool {
    let mut expects = expect.split("[..]");
    if let Some(e) = expects.next() {
        if !output.starts_with(e) {
            return false;
        }
        output = &output[e.len()..];
    }
    for e in expects {
        loop {
            if output.starts_with(e) {
                output = &output[e.len()..];
                break;
            }
            if output.is_empty() {
                return false;
            }
            output = &output[1..];
        }
    }
    output.is_empty()
}

macro_rules! test_print {
    ($name:ident, $($val:expr),*) => {
        #[test]
        fn $name() {
            let expect = concat!($($val),*);
            print(&FIXTURE, stringify!($name), expect);
        }
    }
}

macro_rules! test_diff {
    ($name:ident, $($val:expr),*) => {
        #[test]
        fn $name() {
            let expect = concat!($($val),*);
            diff(&FIXTURE, stringify!($name), expect);
        }
    }
}

mod diff {
    use super::*;
    static FIXTURE: Fixture = Fixture {
        unit: "src/diff.c",
        file1: "tests/bin/diff1",
        file2: "tests/bin/diff2",
    };
    include!("src/diff.rs");
}

mod wasm {
    use super::*;
    static FIXTURE: Fixture = Fixture {
        unit: "src/wasm.c",
        file1: "tests/bin/wasm1",
        file2: "tests/bin/wasm2",
    };
    mod print {
        use super::*;
        include!("src/wasm.rs");
    }
    mod diff {
        use super::*;
        include!("src/wasmdiff.rs");
    }
}
