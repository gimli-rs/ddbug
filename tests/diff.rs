extern crate ddbug;

fn diff(name: &str, expect: &str) {
    let mut flags = flags();
    flags.unit("src/diff.c").name(name);
    let mut diff = Vec::new();
    ddbug::parse_file("tests/bin/diff1", &mut |output_1| {
        ddbug::parse_file("tests/bin/diff2", &mut |output_2| {
            ddbug::diff_file(&mut diff, output_1, output_2, &flags)
        })
    }).unwrap();
    let diff = String::from_utf8(diff).unwrap();
    if !equal(&diff, expect) {
        println!("\nDiff:");
        println!("{}", diff);
        println!("Expected:");
        println!("{}", expect);
        assert_eq!(diff, expect);
    }
}

fn flags<'a>() -> ddbug::Flags<'a> {
    ddbug::Flags {
        calls: false,
        inline_depth: 1,

        category_unit: false,
        category_type: true,
        category_function: true,
        category_variable: true,

        unit: None,
        name: None,
        namespace: Vec::new(),

        sort: ddbug::Sort::None,

        ignore_function_address: true,
        ignore_variable_address: true,
        ..Default::default()
    }
}

fn equal(mut diff: &str, expect: &str) -> bool {
    let mut expects = expect.split("[..]");
    if let Some(e) = expects.next() {
        if !diff.starts_with(e) {
            return false;
        }
        diff = &diff[e.len()..];
    }
    for e in expects {
        loop {
            if diff.starts_with(e) {
                diff = &diff[e.len()..];
                break;
            }
            if diff.is_empty() {
                return false;
            }
            diff = &diff[1..];
        }
    }
    diff.is_empty()
}

macro_rules! test {
    ($name:ident, $($val:expr),*) => {
        #[test]
        fn $name() {
            let expect = concat!($($val),*);
            diff(stringify!($name), expect);
        }
    }
}

include!("src/diff.rs");
