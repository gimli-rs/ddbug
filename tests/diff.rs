extern crate ddbug;
extern crate rand;

use std::fs::{self, File};
use std::io::Write;
use std::process::Command;

// Leading "./" because rustc includes it in the unit DW_AT_name.
const TEST_DIR: &'static str = "./tests/workdir";

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

fn diff(output_file_1: &str, output_file_2: &str, expect: &str, flags: &ddbug::Flags) {
    let mut diff = Vec::new();
    ddbug::parse_file(output_file_1,
                      &mut |output_1| {
        ddbug::parse_file(output_file_2,
                          &mut |output_2| ddbug::diff_file(&mut diff, output_1, output_2, flags))
    })
        .unwrap();
    let diff = String::from_utf8(diff).unwrap();
    if !equal(&diff, expect) {
        println!("\nDiff:");
        println!("{}", diff);
        println!("Expected:");
        println!("{}", expect);
        assert_eq!(diff, expect);
    }
}

fn random_name() -> String {
    let mut s = String::with_capacity(16);
    for _ in 0..4 {
        s.push_str(&format!("{:04x}", rand::random::<u32>()));
    }
    s
}

#[allow(dead_code)]
fn diff_rust(input_1: &str, input_2: &str, expect: &str, flags: &ddbug::Flags) {
    let name = &random_name();
    let input_file = &input_file_rust(name);
    let mut flags = (*flags).clone();
    flags.unit(input_file);
    let output_file_1 = &format!("{}/output1_{}", TEST_DIR, name);
    let output_file_2 = &format!("{}/output2_{}", TEST_DIR, name);
    compile_rust(input_1, input_file, output_file_1);
    compile_rust(input_2, input_file, output_file_2);
    diff(output_file_1, output_file_2, expect, &flags);
    fs::remove_file(input_file).unwrap();
    fs::remove_file(output_file_1).unwrap();
    fs::remove_file(output_file_2).unwrap();
}

fn diff_c(input_1: &str, input_2: &str, expect: &str, flags: &ddbug::Flags) {
    let name = &random_name();
    let input_file = &input_file_c(name);
    let mut flags = (*flags).clone();
    flags.unit(input_file);
    let output_file_1 = &format!("{}/output1_{}", TEST_DIR, name);
    let output_file_2 = &format!("{}/output2_{}", TEST_DIR, name);
    compile_c(input_1, input_file, output_file_1);
    compile_c(input_2, input_file, output_file_2);
    diff(output_file_1, output_file_2, expect, &flags);
    fs::remove_file(input_file).unwrap();
    fs::remove_file(output_file_1).unwrap();
    fs::remove_file(output_file_2).unwrap();
}

#[test]
fn test_typedef_diff_base_equal() {
    diff_c(concat!("typedef char T;\n",
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
    diff_c(concat!("typedef char T;\n",
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
    diff_c(concat!("typedef struct { char c; } T;\n",
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
    diff_c(concat!("typedef struct { char c; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef struct { int i; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("  type T = struct <anon>\n",
                   "- \tsize: 1\n",
                   "+ \tsize: 4\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\tc: char\n",
                   "+ \t\t0[4]\ti: int\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_anon_base() {
    diff_c(concat!("typedef char T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef struct { char c; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("- type T = char\n",
                   "+ type T = struct <anon>\n",
                   "  \tsize: 1\n",
                   "+ \tmembers:\n",
                   "+ \t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_base_anon() {
    diff_c(concat!("typedef struct { char c; } T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef char T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("- type T = struct <anon>\n",
                   "+ type T = char\n",
                   "  \tsize: 1\n",
                   "- \tmembers:\n",
                   "- \t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_typedef_diff_struct_name() {
    diff_c(concat!("struct s1 { char c; };\n",
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
    diff_c(concat!("struct s { char c; };\n",
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

// TODO: typedef_diff_union, typedef_diff_enum, typedef_diff_pointer_anon

#[test]
fn test_struct_diff_defn_equal() {
    diff_c(concat!("struct T { char c; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char c; } s;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_struct_diff_decl_equal() {
    diff_c(concat!("struct T;\n",
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
    diff_c(concat!("struct T { char c; } s;\n",
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
    diff_c(concat!("struct T;\n",
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
    diff_c(concat!("struct T { char c[2]; } s;\n",
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
    diff_c(concat!("struct T { char a; } s;\n",
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

#[test]
fn test_struct_diff_member_reorder() {
    // TODO: T.c should show no difference.
    diff_c(concat!("struct T {",
                   "  char a;",
                   "  char b;",
                   "  char c;",
                   "  char d[2];",
                   "  char x;",
                   "  char y;",
                   "} s;\n",
                   "int main() {}\n"),
           concat!("struct T {",
                   "  char d[2];",
                   "  char c;",
                   "  char a;",
                   "  char b;",
                   "  char x;",
                   "  char z;",
                   "} s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 7\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: char\n",
                   "- \t\t1[1]\tb: char\n",
                   "- \t\t2[1]\tc: char\n",
                   "- \t\t3[2]\td: [char; 2]\n",
                   "+ \t\t0[2]\td: [char; 2]\n",
                   "+ \t\t2[1]\tc: char\n",
                   "+ \t\t3[1]\ta: char\n",
                   "+ \t\t4[1]\tb: char\n",
                   "  \t\t5[1]\tx: char\n",
                   "- \t\t6[1]\ty: char\n",
                   "+ \t\t6[1]\tz: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_struct_diff_recursive_equal() {
    diff_c(concat!("struct T { struct T* a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { struct T* a; } s;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

// TODO test struct padding

#[test]
fn test_union_diff_defn_equal() {
    diff_c(concat!("union T { char c; } s;\n",
                   "int main() {}\n"),
           concat!("union T { char c; } s;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_union_diff_decl_equal() {
    diff_c(concat!("union T;\n",
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
    diff_c(concat!("union T { char c; } s;\n",
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
    diff_c(concat!("union T;\n",
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
    diff_c(concat!("union T { struct { char c[2]; } } s;\n",
                   "int main() {}\n"),
           concat!("union T { struct { char c1; char c2; } } s;\n",
                   "int main() {}\n"),
           concat!("  union T\n",
                   "  \tsize: 2\n",
                   "  \tmembers:\n",
                   "  \t\t0[2]\t<anon>: struct <anon>\n",
                   "- \t\t\t0[2]\tc: [char; 2]\n",
                   "+ \t\t\t0[1]\tc1: char\n",
                   "+ \t\t\t1[1]\tc2: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_union_diff_member() {
    diff_c(concat!("union T { char a; } s;\n",
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

#[test]
fn test_union_diff_member_reorder() {
    diff_c(concat!("union T {",
                   "  char a;",
                   "  char b;",
                   "  char c;",
                   "} s;\n",
                   "int main() {}\n"),
           concat!("union T {",
                   "  char b[2];",
                   "  char a;",
                   "  char c;",
                   "} s;\n",
                   "int main() {}\n"),
           concat!("  union T\n",
                   "- \tsize: 1\n",
                   "+ \tsize: 2\n",
                   "  \tmembers:\n",
                   "  \t\t0[1]\ta: char\n",
                   "- \t\t0[1]\tb: char\n",
                   "+ \t\t0[2]\tb: [char; 2]\n",
                   "  \t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

// TODO test union padding?

#[test]
fn test_member_diff_padding_equal() {
    diff_c(concat!("struct T { char a[2]; int b; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char a[2]; int b; } s;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_member_diff_padding() {
    diff_c(concat!("struct T { char a[1]; int b; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char a[2]; int b; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 8\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: [char; 1]\n",
                   "+ \t\t0[2]\ta: [char; 2]\n",
                   "- \t\t1[3]\t<padding>\n",
                   "+ \t\t2[2]\t<padding>\n",
                   "  \t\t4[4]\tb: int\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_member_diff_padding_none() {
    diff_c(concat!("struct T { char a[1]; int b; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char a[4]; int b; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 8\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: [char; 1]\n",
                   "+ \t\t0[4]\ta: [char; 4]\n",
                   "- \t\t1[3]\t<padding>\n",
                   "  \t\t4[4]\tb: int\n",
                   "\n"),
           flags().name("T"));
}

// Also tests trailing padding.
#[test]
fn test_member_diff_bitfield_equal() {
    diff_c(concat!("struct T { char a; char c:1; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char b; char c:1; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 2\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: char\n",
                   "+ \t\t0[1]\tb: char\n",
                   "  \t\t1[0.1]\tc: char\n",
                   "  \t\t1.1[0.7]\t<padding>\n",
                   "\n"),
           flags().name("T"));
}

// Also tests trailing padding.
#[test]
fn test_member_diff_bitfield() {
    diff_c(concat!("struct T { char a:1; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char a:2; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 1\n",
                   "  \tmembers:\n",
                   "- \t\t0[0.1]\ta: char\n",
                   "+ \t\t0[0.2]\ta: char\n",
                   "- \t\t0.1[0.7]\t<padding>\n",
                   "+ \t\t0.2[0.6]\t<padding>\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_member_diff_unsized() {
    diff_c(concat!("struct T { char a; char b[1]; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char a; char b[]; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "- \tsize: 2\n",
                   "+ \tsize: 1\n",
                   "  \tmembers:\n",
                   "  \t\t0[1]\ta: char\n",
                   "- \t\t1[1]\tb: [char; 1]\n",
                   "+ \t\t1[??]\tb: [char]\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_member_diff_inline_struct_struct_equal() {
    diff_c(concat!("struct T { struct { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { struct { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_member_diff_inline_struct_struct() {
    diff_c(concat!("struct T { struct { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { struct { char c; } a; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 1\n",
                   "  \tmembers:\n",
                   "  \t\t0[1]\ta: struct <anon>\n",
                   "- \t\t\t0[1]\tb: char\n",
                   "+ \t\t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_member_diff_inline_union_union_equal() {
    diff_c(concat!("struct T { union { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { union { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_member_diff_inline_union_union() {
    diff_c(concat!("struct T { union { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { union { char c; } a; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 1\n",
                   "  \tmembers:\n",
                   "  \t\t0[1]\ta: union <anon>\n",
                   "- \t\t\t0[1]\tb: char\n",
                   "+ \t\t\t0[1]\tc: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_member_diff_inline_union_struct() {
    diff_c(concat!("struct T { struct { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { union { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 1\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: struct <anon>\n",
                   "+ \t\t0[1]\ta: union <anon>\n",
                   "- \t\t\t0[1]\tb: char\n",
                   "+ \t\t\t0[1]\tb: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_member_diff_inline_struct_none() {
    diff_c(concat!("struct T { struct { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { char a; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 1\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: struct <anon>\n",
                   "+ \t\t0[1]\ta: char\n",
                   "- \t\t\t0[1]\tb: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_member_diff_inline_none_struct() {
    diff_c(concat!("struct T { char a; } s;\n",
                   "int main() {}\n"),
           concat!("struct T { struct { char b; } a; } s;\n",
                   "int main() {}\n"),
           concat!("  struct T\n",
                   "  \tsize: 1\n",
                   "  \tmembers:\n",
                   "- \t\t0[1]\ta: char\n",
                   "+ \t\t0[1]\ta: struct <anon>\n",
                   "+ \t\t\t0[1]\tb: char\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_enum_diff_equal() {
    diff_c(concat!("enum T { A=1, B=3, C=2 };\n",
                   "enum T t;\n",
                   "int main() {}\n"),
           concat!("enum T { A=1, C=2, B=3 };\n",
                   "enum T t;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_enum_diff() {
    diff_c(concat!("enum T { A=1, B=2, C=3, D=4, E=5 };\n",
                   "enum T t;\n",
                   "int main() {}\n"),
           concat!("enum T { A=1, C=2, B=3, E=5, F=6 };\n",
                   "enum T t;\n",
                   "int main() {}\n"),
           concat!("  enum T\n",
                   "  \tsize: 4\n",
                   "  \tenumerators:\n",
                   "  \t\tA(1)\n",
                   "- \t\tB(2)\n",
                   "+ \t\tC(2)\n",
                   "- \t\tC(3)\n",
                   "+ \t\tB(3)\n",
                   "- \t\tD(4)\n",
                   "  \t\tE(5)\n",
                   "+ \t\tF(6)\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_array_diff_equal() {
    diff_c(concat!("typedef char T[2];\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef char T[2];\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("T"));
}

#[test]
fn test_array_diff_type() {
    diff_c(concat!("typedef char T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef char C;\n",
                   "typedef C T;\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("- type T = char\n",
                   "+ type T = C\n",
                   "  \tsize: 1\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_array_diff_size() {
    diff_c(concat!("typedef char T[1];\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("typedef char T[2];\n",
                   "T t;\n",
                   "int main() {}\n"),
           concat!("- type T = [char; 1]\n",
                   "+ type T = [char; 2]\n",
                   "- \tsize: 1\n",
                   "+ \tsize: 2\n",
                   "\n"),
           flags().name("T"));
}

#[test]
fn test_function_equal() {
    diff_c(concat!("char F(char a, char b) {}\n",
                   "int main() {}\n"),
           concat!("char F(char a, char b) {}\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("F"));
}

#[test]
fn test_function_diff_return_type() {
    diff_c(concat!("char F() {}\n",
                   "int main() {}\n"),
           concat!("int F() {}\n",
                   "int main() {}\n"),
           concat!("  fn F\n",
                   "[..]\n",
                   "  \treturn type:\n",
                   "- \t\t[1]\tchar\n",
                   "+ \t\t[4]\tint\n",
                   "\n"),
           flags().name("F"));
}

#[test]
fn test_function_diff_parameters() {
    diff_c(concat!("char F(char a, char c, char d, char e) {}\n",
                   "int main() {}\n"),
           concat!("char F(char b, char c, int d, char f) {}\n",
                   "int main() {}\n"),
           concat!("  fn F\n",
                   "[..]\n",
                   "  \treturn type:\n",
                   "  \t\t[1]\tchar\n",
                   "  \tparameters:\n",
                   "- \t\t[1]\ta: char\n",
                   "+ \t\t[1]\tb: char\n",
                   "  \t\t[1]\tc: char\n",
                   "- \t\t[1]\td: char\n",
                   "+ \t\t[4]\td: int\n",
                   "- \t\t[1]\te: char\n",
                   "+ \t\t[1]\tf: char\n",
                   "\n"),
           flags().name("F"));
}

#[test]
fn test_variable_equal() {
    diff_c(concat!("char V;\n",
                   "int main() {}\n"),
           concat!("char V;\n",
                   "int main() {}\n"),
           concat!(""),
           flags().name("V"));
}

#[test]
fn test_variable_diff_size() {
    diff_c(concat!("char V[1];\n",
                   "int main() {}\n"),
           concat!("char V[2];\n",
                   "int main() {}\n"),
           concat!("- var V: [char; 1]\n",
                   "+ var V: [char; 2]\n",
                   "- \tsize: 1\n",
                   "+ \tsize: 2\n",
                   "\n"),
           flags().name("V"));
}

#[test]
fn test_variable_diff_decl() {
    diff_c(concat!("char **environ;\n",
                   "int main() {}\n"),
           concat!("extern char **environ;\n",
                   "int main() { environ == 0; }\n"),
           concat!("  var environ: * * char\n",
                   "  \tsize: 8\n",
                   "+ \tdeclaration: yes\n",
                   "\n"),
           flags().name("environ"));
}
