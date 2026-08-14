#define CONCAT(a, b) a ## _ ## b
#define STRING(T) #T

#define S(T) STRING(T)

#if defined(TEST1) || defined(TEST2)
#define TEST
#endif

#if defined(TESTRS)
#define EXPECT(T, ...) test_print!(T, __VA_ARGS__);
#endif

#if defined(TESTDIFFRS)
#define EXPECT_DIFF(T, ...) test_diff!(T, __VA_ARGS__);
#endif

#ifndef EXPECT
#define EXPECT(T, ...)
#endif

#ifndef EXPECT_DIFF
#define EXPECT_DIFF(T, ...)
#endif

#ifdef TEST
int sink(int);
int sink_pointer(int *);
#endif

///////////////////////////////////////////////////////////
// Tests

// Parameters in Wasm locals
// Local variable on shadow stack or Wasm operand stack or in Wasm local.
#undef T
#define T wasm_local
#ifdef TEST
int T(int a, int b) {
    int local = a + b;
#ifdef TEST1
    sink_pointer(&local);
#endif
#ifdef TEST2
    sink(local);
#endif
    return local;
}
#endif
EXPECT_DIFF(
    T,
    "  fn ", S(T), "\n",
    "[..]\n",
    "  \tparameters:\n",
    "  \t\t[4]\ta: int\n",
    "  \t\t\tlocation: wasm local 0\n",
    "  \t\t[4]\tb: int\n",
    "  \t\t\tlocation: wasm local 1\n",
    "  \tvariables:\n",
    "  \t\t[4]\tlocal: int\n",
    "  \t\t\tlocations:\n",
    "- \t\t\t\tframe+0xc\n",
    "+ \t\t\t\twasm local 0\n",
    "+ \t\t\t\twasm stack 0\n",
    "\n")

// Parameter passed by reference (DW_OP_WASM_location with no DW_OP_stack_value).
#undef T
#define T wasm_indirect
#ifdef TEST
struct big { long long a, b, c; };

__attribute__((optnone)) long long T(struct big s) {
    return s.a;
}
#endif
EXPECT(
    T,
    "fn ", S(T), "\n",
    "[..]\n",
    "\tparameters:\n",
    "\t\t[24]\ts: struct big\n",
    "\t\t\tlocation: wasm local 0+0x0\n",
    "\n")
