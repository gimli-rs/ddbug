test_diff!(wasm_local, "  fn ", "wasm_local", "\n", "[..]\n", "  \tparameters:\n", "  \t\t[4]\ta: int\n", "  \t\t\tlocation: wasm local 0\n", "  \t\t[4]\tb: int\n", "  \t\t\tlocation: wasm local 1\n", "  \tvariables:\n", "  \t\t[4]\tlocal: int\n", "  \t\t\tlocations:\n", "- \t\t\t\tframe+0xc\n", "+ \t\t\t\twasm local 0\n", "+ \t\t\t\twasm stack 0\n", "\n");

