#define CONCAT(a, b) a ## _ ## b
#define NAME(T, name) CONCAT(T, name)

#define EXPAND(T) T
#define STRING(T) #T

#define S(T) STRING(T)

#define X_USE_TYPE(T) T *use_ ## T
#define USE_TYPE(T) X_USE_TYPE(T)

#define X_USE_STRUCT(T) struct T *use_ ## T
#define USE_STRUCT(T) X_USE_STRUCT(T)

#define X_USE_UNION(T) union T *use_ ## T
#define USE_UNION(T) X_USE_UNION(T)

#define X_USE_ENUM(T) enum T use_ ## T
#define USE_ENUM(T) X_USE_ENUM(T)

#define X_USE_VAR(type, T) type * use_ ## T = & T
#define USE_VAR(type, T) X_USE_VAR(type, T)

#if defined(TEST1) || defined(TEST2)
#define TEST
int main() {}
#endif

#if defined(TESTRS)
#define EXPECT(T, ...) \
    test!(T, __VA_ARGS__);
#else
#define EXPECT(T, ...)
#endif


///////////////////////////////////////////////////////////
// Tests

#undef T
#define T typedef_diff_base_equal
#define name NAME(T)
#ifdef TEST
    typedef char T;
    USE_TYPE(T);
#endif
EXPECT(T, "")

#undef T
#define T typedef_diff_base
#ifdef TEST1
    typedef char T;
    USE_TYPE(T);
#endif
#ifdef TEST2
    typedef int T;
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "- type ", S(T), " = char\n",
    "+ type ", S(T), " = int\n",
    "- \tsize: 1\n",
    "+ \tsize: 4\n",
    "\n")

#undef T
#define T typedef_diff_anon_equal
#ifdef TEST
    typedef struct {
        char c;
    } T;
    USE_TYPE(T);
#endif
EXPECT(T, "")

#undef T
#define T typedef_diff_anon
#ifdef TEST1
    typedef struct {
        char c;
    } T;
    USE_TYPE(T);
#endif
#ifdef TEST2
    typedef struct {
        int i;
    } T;
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "  type ", S(T), " = struct <anon>\n",
    "- \tsize: 1\n",
    "+ \tsize: 4\n",
    "  \tmembers:\n",
    "- \t\t0[1]\tc: char\n",
    "+ \t\t0[4]\ti: int\n",
    "\n")

#undef T
#define T typedef_diff_anon_base
#ifdef TEST1
    typedef char T;
    USE_TYPE(T);
#endif
#ifdef TEST2
    typedef struct {
        char c;
    } T;
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "- type ", S(T), " = char\n",
    "+ type ", S(T), " = struct <anon>\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "+ \t\t0[1]\tc: char\n",
    "\n")

// Even though they have the same members, it is not meaningful to diff them.
#undef T
#define T typedef_diff_anon_struct_union
#ifdef TEST1
    typedef struct {
        char c;
    } T;
    USE_TYPE(T);
#endif
#ifdef TEST2
    typedef union {
        char c;
    } T;
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "- type ", S(T), " = struct <anon>\n",
    "+ type ", S(T), " = union <anon>\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "- \t\t0[1]\tc: char\n",
    "+ \t\t0[1]\tc: char\n",
    "\n")

#undef T
#define T typedef_diff_base_anon
#ifdef TEST1
    typedef struct {
        char c;
    } T;
    USE_TYPE(T);
#endif
#ifdef TEST2
    typedef char T;
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "- type ", S(T), " = struct <anon>\n",
    "+ type ", S(T), " = char\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "- \t\t0[1]\tc: char\n",
    "\n")

#undef T
#define T typedef_diff_struct_name
#ifdef TEST1
    struct NAME(T, s1) {
        char c;
    };
    typedef struct NAME(T, s1) T;
    USE_TYPE(T);
#endif
#ifdef TEST2
    struct NAME(T, s2) {
        char c;
    };
    typedef struct NAME(T, s2) T;
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "- type ", S(T), " = struct ", S(NAME(T, s1)), "\n",
    "+ type ", S(T), " = struct ", S(NAME(T, s2)), "\n",
    "  \tsize: 1\n",
    "\n")

#undef T
#define T typedef_diff_struct_size
#ifdef TEST1
    struct s {
        char c;
    };
    typedef struct s T;
    USE_TYPE(T);
#endif
#ifdef TEST2
    struct s {
        int i;
    };
    typedef struct s T;
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "  type ", S(T), " = struct s\n",
    "- \tsize: 1\n",
    "+ \tsize: 4\n",
    "\n")

// TODO: typedef_diff_union, typedef_diff_enum, typedef_diff_pointer_anon

#undef T
#define T struct_diff_defn_equal
#ifdef TEST
    struct T {
        char c;
    };
    USE_STRUCT(T);
#endif
EXPECT(T, "")

#undef T
#define T struct_diff_decl_equal
#ifdef TEST
    struct T;
    USE_STRUCT(T);
#endif
EXPECT(T, "")

#undef T
#define T struct_diff_defn_decl
#ifdef TEST1
    struct T {
        char c;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T;
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "+ \tdeclaration: yes\n",
    "- \tsize: 1\n",
    "  \tmembers:\n",
    "- \t\t0[1]\tc: char\n",
    "\n")

#undef T
#define T struct_diff_decl_defn
#ifdef TEST1
    struct T;
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char c;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "- \tdeclaration: yes\n",
    "+ \tsize: 1\n",
    "  \tmembers:\n",
    "+ \t\t0[1]\tc: char\n",
    "\n")

#undef T
#define T struct_diff_size_equal
#ifdef TEST1
    struct T {
        char c[2];
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char c1;
        char c2;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 2\n",
    "  \tmembers:\n",
    "- \t\t0[2]\tc: [char; 2]\n",
    "+ \t\t0[1]\tc1: char\n",
    "+ \t\t1[1]\tc2: char\n",
    "\n")

#undef T
#define T struct_diff_member
#ifdef TEST1
    struct T {
        char a;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        int a;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "- \tsize: 1\n",
    "+ \tsize: 4\n",
    "  \tmembers:\n",
    "- \t\t0[1]\ta: char\n",
    "+ \t\t0[4]\ta: int\n",
    "\n")

#undef T
#define T struct_diff_member_reorder
#ifdef TEST1
    struct T {
        char a;
        char b;
        char c;
        char d[2];
        char x;
        char y;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char d[2];
        char c;
        char a;
        char b;
        char x;
        char z;
    };
    USE_STRUCT(T);
#endif
// TODO: T.c should show no difference?
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 7\n",
    "  \tmembers:\n",
    "+ \t\t0[2]\td: [char; 2]\n",
    "+ \t\t2[1]\tc: char\n",
    "- \t\t0[1]\ta: char\n",
    "+ \t\t3[1]\ta: char\n",
    "- \t\t1[1]\tb: char\n",
    "+ \t\t4[1]\tb: char\n",
    "- \t\t2[1]\tc: char\n",
    "- \t\t3[2]\td: [char; 2]\n",
    "  \t\t5[1]\tx: char\n",
    "- \t\t6[1]\ty: char\n",
    "+ \t\t6[1]\tz: char\n",
    "\n")

#undef T
#define T struct_diff_recursive_equal
#ifdef TEST
    struct T {
        struct T* a;
    };
    USE_STRUCT(T);
#endif
EXPECT(T, "")

// TODO test struct padding

#undef T
#define T union_diff_defn_equal
#ifdef TEST
    union T {
        char c;
    };
    USE_UNION(T);
#endif
EXPECT(T, "")

#undef T
#define T union_diff_decl_equal
#ifdef TEST
    union T;
    USE_UNION(T);
#endif
EXPECT(T, "")

#undef T
#define T union_diff_defn_decl
#ifdef TEST1
    union T {
        char c;
    };
    USE_UNION(T);
#endif
#ifdef TEST2
    union T;
    USE_UNION(T);
#endif
EXPECT(
    T,
    "  union ", S(T), "\n",
    "+ \tdeclaration: yes\n",
    "- \tsize: 1\n",
    "  \tmembers:\n",
    "- \t\t0[1]\tc: char\n",
    "\n")


#undef T
#define T union_diff_decl_defn
#ifdef TEST1
    union T;
    USE_UNION(T);
#endif
#ifdef TEST2
    union T {
        char c;
    };
    USE_UNION(T);
#endif
EXPECT(
    T,
    "  union ", S(T), "\n",
    "- \tdeclaration: yes\n",
    "+ \tsize: 1\n",
    "  \tmembers:\n",
    "+ \t\t0[1]\tc: char\n",
    "\n")

#undef T
#define T union_diff_size_equal
#ifdef TEST1
    union T {
        struct {
            char c[2];
        };
    };
    USE_UNION(T);
#endif
#ifdef TEST2
    union T {
        struct {
            char c1;
            char c2;
        };
    };
    USE_UNION(T);
#endif
EXPECT(
    T,
    "  union ", S(T), "\n",
    "  \tsize: 2\n",
    "  \tmembers:\n",
    "  \t\t0[2]\t<anon>: struct <anon>\n",
    "- \t\t\t0[2]\tc: [char; 2]\n",
    "+ \t\t\t0[1]\tc1: char\n",
    "+ \t\t\t1[1]\tc2: char\n",
    "\n")

#undef T
#define T union_diff_member
#ifdef TEST1
    union T {
        char a;
    };
    USE_UNION(T);
#endif
#ifdef TEST2
    union T {
        int a;
    };
    USE_UNION(T);
#endif
EXPECT(
    T,
    "  union ", S(T), "\n",
    "- \tsize: 1\n",
    "+ \tsize: 4\n",
    "  \tmembers:\n",
    "- \t\t0[1]\ta: char\n",
    "+ \t\t0[4]\ta: int\n",
    "\n")

#undef T
#define T union_diff_member_reorder
#ifdef TEST1
    union T {
      char a;
      char b;
      char c;
    };
    USE_UNION(T);
#endif
#ifdef TEST2
    union T {
      char b[2];
      char a;
      char c;
    };
    USE_UNION(T);
#endif
EXPECT(
    T,
    "  union ", S(T), "\n",
    "- \tsize: 1\n",
    "+ \tsize: 2\n",
    "  \tmembers:\n",
    "+ \t\t0[2]\tb: [char; 2]\n",
    "  \t\t0[1]\ta: char\n",
    "- \t\t0[1]\tb: char\n",
    "  \t\t0[1]\tc: char\n",
    "\n")

// TODO test union padding?

#undef T
#define T member_diff_padding_equal
#ifdef TEST
    struct T {
        char a[2];
        int b;
    };
    USE_STRUCT(T);
#endif
EXPECT(T, "")

#undef T
#define T member_diff_padding
#ifdef TEST1
    struct T {
        char a[1];
        int b;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char a[2];
        int b;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 8\n",
    "  \tmembers:\n",
    "- \t\t0[1]\ta: [char; 1]\n",
    "+ \t\t0[2]\ta: [char; 2]\n",
    "- \t\t1[3]\t<padding>\n",
    "+ \t\t2[2]\t<padding>\n",
    "  \t\t4[4]\tb: int\n",
    "\n")

#undef T
#define T member_diff_padding_none
#ifdef TEST1
    struct T {
        char a[1];
        int b;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char a[4];
        int b;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 8\n",
    "  \tmembers:\n",
    "- \t\t0[1]\ta: [char; 1]\n",
    "+ \t\t0[4]\ta: [char; 4]\n",
    "- \t\t1[3]\t<padding>\n",
    "  \t\t4[4]\tb: int\n",
    "\n")

// Also tests trailing padding.
#undef T
#define T member_diff_bitfield_equal
#ifdef TEST1
    struct T {
        char a;
        char c:1;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char b;
        char c:1;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 2\n",
    "  \tmembers:\n",
    "- \t\t0[1]\ta: char\n",
    "+ \t\t0[1]\tb: char\n",
    "  \t\t1[0.1]\tc: char\n",
    "  \t\t1.1[0.7]\t<padding>\n",
    "\n")

// Also tests trailing padding.
#undef T
#define T member_diff_bitfield
#ifdef TEST1
    struct T {
        char a:1;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char a:2;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "- \t\t0[0.1]\ta: char\n",
    "+ \t\t0[0.2]\ta: char\n",
    "- \t\t0.1[0.7]\t<padding>\n",
    "+ \t\t0.2[0.6]\t<padding>\n",
    "\n")

#undef T
#define T member_diff_unsized
#ifdef TEST1
    struct T {
        char a;
        char b[1];
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char a;
        char b[];
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "- \tsize: 2\n",
    "+ \tsize: 1\n",
    "  \tmembers:\n",
    "  \t\t0[1]\ta: char\n",
    "- \t\t1[1]\tb: [char; 1]\n",
    "+ \t\t1[??]\tb: [char; ??]\n",
    "\n")

#undef T
#define T member_diff_inline_struct_struct_equal
#ifdef TEST
    struct T {
        struct {
            char b;
        } a;
    };
    USE_STRUCT(T);
#endif
EXPECT(T, "")

#undef T
#define T member_diff_inline_struct_struct
#ifdef TEST1
    struct T {
        struct {
            char b;
        } a;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        struct {
            char c;
        } a;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "  \t\t0[1]\ta: struct <anon>\n",
    "- \t\t\t0[1]\tb: char\n",
    "+ \t\t\t0[1]\tc: char\n",
    "\n")

#undef T
#define T member_diff_inline_union_union_equal
#ifdef TEST
    struct T {
        union {
            char b;
        } a;
    };
    USE_STRUCT(T);
#endif
EXPECT(T, "")

#undef T
#define T member_diff_inline_union_union
#ifdef TEST1
    struct T {
        union {
            char b;
        } a;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        union {
            char c;
        } a;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "  \t\t0[1]\ta: union <anon>\n",
    "- \t\t\t0[1]\tb: char\n",
    "+ \t\t\t0[1]\tc: char\n",
    "\n")

#undef T
#define T member_diff_inline_union_struct
#ifdef TEST1
    struct T {
        struct {
            char b;
        } a;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        union {
            char b;
        } a;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "- \t\t0[1]\ta: struct <anon>\n",
    "+ \t\t0[1]\ta: union <anon>\n",
    "- \t\t\t0[1]\tb: char\n",
    "+ \t\t\t0[1]\tb: char\n",
    "\n")

#undef T
#define T member_diff_inline_struct_none
#ifdef TEST1
    struct T {
        struct {
            char b;
        } a;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        char a;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "- \t\t0[1]\ta: struct <anon>\n",
    "+ \t\t0[1]\ta: char\n",
    "- \t\t\t0[1]\tb: char\n",
    "\n")

#undef T
#define T member_diff_inline_none_struct
#ifdef TEST1
    struct T {
        char a;
    };
    USE_STRUCT(T);
#endif
#ifdef TEST2
    struct T {
        struct {
            char b;
        } a;
    };
    USE_STRUCT(T);
#endif
EXPECT(
    T,
    "  struct ", S(T), "\n",
    "  \tsize: 1\n",
    "  \tmembers:\n",
    "- \t\t0[1]\ta: char\n",
    "+ \t\t0[1]\ta: struct <anon>\n",
    "+ \t\t\t0[1]\tb: char\n",
    "\n")

#undef T
#define T enum_diff_equal
#ifdef TEST
    enum T {
        A1=1,
        B1=2,
        C1=3,
    };
    USE_ENUM(T);
#endif
EXPECT(T, "")

#undef T
#define T enum_diff
#ifdef TEST1
    enum T {
        A2=1,
        B2=2,
        C2=3,
        D2=4,
        E2=5,
    };
    USE_ENUM(T);
#endif
#ifdef TEST2
    enum T {
        A2=1,
        C2=2,
        B2=3,
        E2=5,
        F2=6,
    };
    USE_ENUM(T);
#endif
EXPECT(
    T,
    "  enum ", S(T), "\n",
    "  \tsize: 4\n",
    "  \tenumerators:\n",
    "  \t\tA2(1)\n",
    "- \t\tB2(2)\n",
    "+ \t\tC2(2)\n",
    "- \t\tC2(3)\n",
    "+ \t\tB2(3)\n",
    "- \t\tD2(4)\n",
    "  \t\tE2(5)\n",
    "+ \t\tF2(6)\n",
    "\n")

#undef T
#define T array_diff_equal
#ifdef TEST
    typedef char T[2];
    USE_TYPE(T);
#endif
EXPECT(T, "")

#undef T
#define T array_diff_type
#ifdef TEST1
    typedef char T;
    USE_TYPE(T);
#endif
#ifdef TEST2
    typedef char C;
    typedef C T;
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "- type ", S(T), " = char\n",
    "+ type ", S(T), " = C\n",
    "  \tsize: 1\n",
    "\n")

#undef T
#define T array_diff_size
#ifdef TEST1
    typedef char T[1];
    USE_TYPE(T);
#endif
#ifdef TEST2
    typedef char T[2];
    USE_TYPE(T);
#endif
EXPECT(
    T,
    "- type ", S(T), " = [char; 1]\n",
    "+ type ", S(T), " = [char; 2]\n",
    "- \tsize: 1\n",
    "+ \tsize: 2\n",
    "\n")

#undef T
#define T function_equal
#ifdef TEST
    char T(char a, char b) {}
#endif
EXPECT(T, "")

#undef T
#define T function_diff_return_type
#ifdef TEST1
    char T() {}
#endif
#ifdef TEST2
    int T() {}
#endif
EXPECT(
    T,
    "  fn ", S(T), "\n",
    "[..]\n",
    "  \treturn type:\n",
    "- \t\t[1]\tchar\n",
    "+ \t\t[4]\tint\n",
    "\n")

/* TODO: requires fuzzy parameter cmp */
#if 0
#undef T
#define T function_diff_parameters
#ifdef TEST1
    char T(char a, char c, char d, char e, int extra, char g) {}
#endif
#ifdef TEST2
    char T(char b, char c, int d, char f, char g) {}
#endif
EXPECT(
    T,
    "  fn ", S(T), "\n",
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
    "- \t\t[4]\textra: int\n",
    "  \t\t[1]\tg: char\n",
    "\n")
#endif

#undef T
#define T function_diff_variables
#ifdef TEST1
    void T(void) { char a; char c; char d; char e; int extra; char g; }
#endif
#ifdef TEST2
    void T(void) { char b; int d; char c; char f; char g; }
#endif
EXPECT(
    T,
    "  fn ", S(T), "\n",
    "[..]\n",
    "  \tvariables:\n",
    "- \t\t[1]\ta: char\n",
    "+ \t\t[1]\tb: char\n",
    "  \t\t[1]\tc: char\n",
    "- \t\t[1]\td: char\n",
    "+ \t\t[4]\td: int\n",
    "- \t\t[1]\te: char\n",
    "+ \t\t[1]\tf: char\n",
    "- \t\t[4]\textra: int\n",
    "  \t\t[1]\tg: char\n",
    "\n")

#undef T
#define T variable_equal
#ifdef TEST
    char T;
#endif
EXPECT(T, "")

#undef T
#define T variable_diff_size
#ifdef TEST1
    char T[1];
#endif
#ifdef TEST2
    char T[2];
#endif
EXPECT(
    T,
    "- var ", S(T), ": [char; 1]\n",
    "+ var ", S(T), ": [char; 2]\n",
    "[..]",
    "- \tsize: 1\n",
    "+ \tsize: 2\n",
    "\n")

#undef T
#define T variable_diff_size_multi
#ifdef TEST1
    char T[1][3];
#endif
#ifdef TEST2
    char T[2][4];
#endif
EXPECT(
    T,
    "- var ", S(T), ": [char; 1, 3]\n",
    "+ var ", S(T), ": [char; 2, 4]\n",
    "[..]",
    "- \tsize: 3\n",
    "+ \tsize: 8\n",
    "\n")

#undef T
#define T variable_diff_decl
#ifdef SUPPORT
    int T;
#endif
#ifdef TEST1
    int T;
#endif
#ifdef TEST2
    extern int T;
    USE_VAR(int, T);
#endif
EXPECT(
    T,
    "  var ", S(T), ": int\n",
    "[..]",
    "  \tsize: 4\n",
    "+ \tdeclaration: yes\n",
    "\n")
