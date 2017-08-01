all: src/diff.rs bin/diff1 bin/diff2

src/diff.rs: src/diff.c
	gcc -E -P -trigraphs -D TESTRS $^ -o $@

bin/diff1: src/diff.c src/support.c
	gcc -fdebug-prefix-map=`pwd`= -g -D TEST1 $^ -o $@

bin/diff2: src/diff.c src/support.c
	gcc -fdebug-prefix-map=`pwd`= -g -D TEST2 $^ -o $@
