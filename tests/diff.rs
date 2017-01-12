extern crate ddbug;

use std::fs::{self, File};
use std::io::Write;
use std::process::Command;

const TEST_DIR: &'static str = "tests/workdir";

fn write_input(input_file: &str, input_text: &str) {
    fs::create_dir_all(TEST_DIR).unwrap();
    let mut input = File::create(input_file).unwrap();
    input.write_all(input_text.as_bytes()).unwrap();
}

fn input_file_rust(name: &str) -> String {
    format!("{}/input_{}.rs", TEST_DIR, name)
}

fn input_file_c(name: &str) -> String {
    format!("{}/input_{}.c", TEST_DIR, name)
}

fn compile_rust(input_text: &str, input_file: &str, output_file: &str) {
    write_input(input_file, input_text);
    let output = Command::new("rustc")
        .arg("-g")
        .arg("-o")
        .arg(output_file)
        .arg(input_file)
        .output()
        .unwrap();
    assert!(output.status.success());
}

fn compile_c(input_text: &str, input_file: &str, output_file: &str) {
    write_input(input_file, input_text);
    let output = Command::new("cc")
        .arg("-g")
        .arg("-o")
        .arg(output_file)
        .arg(input_file)
        .output()
        .unwrap();
    assert!(output.status.success());
}

fn flags() -> ddbug::Flags<'static> {
    ddbug::Flags {
        calls: false,
        sort: false,
        inline_depth: 1,
        unit: None,
        name: None,
        namespace: Vec::new(),
    }
}

fn diff(output_file_1: &str, output_file_2: &str, expect: &str, flags: &ddbug::Flags) {
    let mut diff = Vec::new();
    ddbug::parse_file(output_file_1,
                      &mut |output_1| {
        ddbug::parse_file(output_file_2,
                          &mut |output_2| ddbug::diff_file(&mut diff, output_1, output_2, flags))
    })
        .unwrap();
    let diff = String::from_utf8(diff).unwrap();
    if diff != expect {
        println!("\nDiff:");
        println!("{}", diff);
        println!("Expected:");
        println!("{}", expect);
        assert_eq!(diff, expect);
    }
}

#[allow(dead_code)]
fn diff_rust(name: &str, input_1: &str, input_2: &str, expect: &str, flags: &ddbug::Flags) {
    let input_file = &input_file_rust(name);
    let mut flags = (*flags).clone();
    flags.unit(input_file);
    let output_file_1 = &format!("{}/output1_{}", TEST_DIR, name);
    let output_file_2 = &format!("{}/output2_{}", TEST_DIR, name);
    compile_rust(input_1, input_file, output_file_1);
    compile_rust(input_2, input_file, output_file_2);
    diff(output_file_1, output_file_2, expect, &flags);
}

fn diff_c(name: &str, input_1: &str, input_2: &str, expect: &str, flags: &ddbug::Flags) {
    let input_file = &input_file_c(name);
    let mut flags = (*flags).clone();
    flags.unit(input_file);
    let output_file_1 = &format!("{}/output1_{}", TEST_DIR, name);
    let output_file_2 = &format!("{}/output2_{}", TEST_DIR, name);
    compile_c(input_1, input_file, output_file_1);
    compile_c(input_2, input_file, output_file_2);
    diff(output_file_1, output_file_2, expect, &flags);
}

#[test]
fn test_typedef_diff_base_equal() {
    diff_c("typedef_diff_base_equal",
           concat!("typedef char T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef char T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_base() {
    diff_c("typedef_diff_base",
           concat!("typedef char T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef int T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("- type T = char\n",
                   "+ type T = int\n",
                   "- \tsize: 1\n",
                   "+ \tsize: 4\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_anon_equal() {
    // Same anon struct.
    diff_c("typedef_diff_anon_equal",
           concat!("typedef struct { char c; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef struct { char c; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_anon() {
    // Different anon struct.
    diff_c("typedef_diff_anon",
           concat!("typedef struct { char c; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef struct { int i; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("  type T = \n",
                   "  \tstruct <anon>\n",
                   "- \t\tsize: 1\n",
                   "+ \t\tsize: 4\n",
                   "  \t\tmembers:\n",
                   "- \t\t\t0[1]\tc: char\n",
                   "+ \t\t\t0[4]\ti: int\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_anon_base() {
    diff_c("typedef_diff_anon_base",
           concat!("typedef char T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef struct { char c; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("- type T = char\n",
                   "- \tsize: 1\n",
                   // TODO: no newline here
                   "\n",
                   "+ type T = \n",
                   "+ \tstruct <anon>\n",
                   "+ \t\tsize: 1\n",
                   "+ \t\tmembers:\n",
                   "+ \t\t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_base_anon() {
    diff_c("typedef_diff_base_anon",
           concat!("typedef struct { char c; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef char T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("- type T = \n",
                   "- \tstruct <anon>\n",
                   "- \t\tsize: 1\n",
                   "- \t\tmembers:\n",
                   "- \t\t\t0[1]\tc: char\n",
                   // TODO: no newline here
                   "\n",
                   "+ type T = char\n",
                   "+ \tsize: 1\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_struct_name() {
    diff_c("typedef_diff_struct_name",
           concat!("struct s1 { char c; };\n",
                   "typedef struct s1 T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("struct s2 { char c; };\n",
                   "typedef struct s2 T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("- type T = struct s1\n",
                   "+ type T = struct s2\n",
                   "  \tsize: 1\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_struct_size() {
    diff_c("typedef_diff_struct_size",
           concat!("struct s { char c; };\n",
                   "typedef struct s T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("struct s { int i; };\n",
                   "typedef struct s T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("  type T = struct s\n",
                   "- \tsize: 1\n",
                   "+ \tsize: 4\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_struct_diff_defn_equal() {
    diff_c("struct_diff_defn_equal",
           concat!("struct T { char c; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char c; } s;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_struct_diff_decl_equal() {
    diff_c("struct_diff_decl_equal",
           concat!("struct T;\n",
                   "struct T *p;\n",
                   "int main() {}\n"),
           concat!("struct T;\n",
                   "struct T *p;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_struct_diff_defn_decl() {
    diff_c("struct_diff_defn_decl",
           concat!("struct T { char c; } s;\n",
                   "int main() {}\n"),
           concat!("struct T;\n",
                   "struct T *p;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "- \tsize: 1\n",
                   "+ \tdeclaration: yes\n",
                   "- \tmembers:\n",
                   "- \t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_struct_diff_decl_defn() {
    diff_c("struct_diff_decl_defn",
           concat!("struct T;\n",
                   "struct T *p;\n",
                   "int main() {}\n"),
           concat!("struct T { char c; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "+ \tsize: 1\n",
                   "- \tdeclaration: yes\n",
                   "+ \tmembers:\n",
                   "+ \t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_struct_diff_size_equal() {
    diff_c("struct_diff_size_equal",
           concat!("struct T { char c[2]; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char c1; char c2; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 2\n",
                   "  \tmembers:\n",
                   "- \t\t0[2]\tc: [char; 2]\n",
                   "+ \t\t0[1]\tc1: char\n",
                   "+ \t\t1[1]\tc2: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_struct_diff_member() {
    diff_c("struct_diff_member",
           concat!("struct T { char a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { int a; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "- \tsize: 1\n",
                   "+ \tsize: 4\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: char\n",
                   "+ \t\t0[4]\ta: int\n",
                   "\n"),
           flags().name("T"));
}

// TODO test struct padding

#[test]
fn test_union_diff_defn_equal() {
    diff_c("union_diff_defn_equal",
           concat!("union T { char c; } s;\n",
                   "int main() {}\n"),
           concat!("union T { char c; } s;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_union_diff_decl_equal() {
    diff_c("union_diff_decl_equal",
           concat!("union T;\n",
                   "union T *p;\n",
                   "int main() {}\n"),
           concat!("union T;\n",
                   "union T *p;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_union_diff_defn_decl() {
    diff_c("union_diff_defn_decl",
           concat!("union T { char c; } s;\n",
                   "int main() {}\n"),
           concat!("union T;\n",
                   "union T *p;\n",
                   "int main() {}\n"),
           concat!("  union T\n",
                   "- \tsize: 1\n",
                   "+ \tdeclaration: yes\n",
                   "- \tmembers:\n",
                   "- \t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_union_diff_decl_defn() {
    diff_c("union_diff_decl_defn",
           concat!("union T;\n",
                   "union T *p;\n",
                   "int main() {}\n"),
           concat!("union T { char c; } s;\n",
                   "int main() {}\n"),
           concat!("  union T\n",
                   "+ \tsize: 1\n",
                   "- \tdeclaration: yes\n",
                   "+ \tmembers:\n",
                   "+ \t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_union_diff_size_equal() {
    diff_c("union_diff_size_equal",
           concat!("union T { struct { char c[2]; } } s;\n",
                   "int main() {}\n"),
           concat!("union T { struct { char c1; char c2; } } s;\n",
                   "int main() {}\n"),
           concat!("  union T\n",
                   "  \tsize: 2\n",
                   "  \tmembers:\n",
                   // TODO: merge anon members
                   "- \t\t0[2]\t<anon>: struct <anon>\n",
                   "- \t\t\t0[2]\tc: [char; 2]\n",
                   "+ \t\t0[2]\t<anon>: struct <anon>\n",
                   "+ \t\t\t0[1]\tc1: char\n",
                   "+ \t\t\t1[1]\tc2: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_union_diff_member() {
    diff_c("union_diff_member",
           concat!("union T { char a; } s;\n",
                   "int main() {}\n"),
           concat!("union T { int a; } s;\n",
                   "int main() {}\n"),
           concat!("  union T\n",
                   "- \tsize: 1\n",
                   "+ \tsize: 4\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: char\n",
                   "+ \t\t0[4]\ta: int\n",
                   "\n"),
           flags().name("T"));
}

// TODO test union padding?
