all: src/diff.rs src/wasm.rs src/wasmdiff.rs bin/diff1 bin/diff2 bin/wasm1 bin/wasm2

src/diff.rs: src/diff.c
	gcc -E -P -trigraphs -D TESTRS $^ -o $@

src/wasm.rs: src/wasm.c
	gcc -E -P -trigraphs -D TESTRS $^ -o $@

src/wasmdiff.rs: src/wasm.c
	gcc -E -P -trigraphs -D TESTDIFFRS $^ -o $@

bin/diff1: src/diff.c src/support.c
	gcc -fdebug-prefix-map=`pwd`= -g -D TEST1 $^ -o $@

bin/diff2: src/diff.c src/support.c
	gcc -fdebug-prefix-map=`pwd`= -g -D TEST2 $^ -o $@

WASMFLAGS=--target=wasm32 --no-wasm-opt -nostdlib -Wl,--no-entry -Wl,--export-all -Wl,--allow-undefined

bin/wasm1: src/wasm.c
	clang $(WASMFLAGS) -fdebug-prefix-map=`pwd`= -g -O2 -D TEST1 $^ -o $@

bin/wasm2: src/wasm.c
	clang $(WASMFLAGS) -fdebug-prefix-map=`pwd`= -g -O2 -D TEST2 $^ -o $@
