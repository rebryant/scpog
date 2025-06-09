CC=gcc
OPT=-O3

CFLAGS= $(OPT) -g -Wno-nullability-completeness

all: cpog-check cpog-check-sequential

q25.o: q25.c q25.h
	$(CC) $(CFLAGS) -c q25.c

cpog-check-sequential: cpog-check.c q25.o
	$(CC) $(CFLAGS) cpog-check.c q25.o -o cpog-check-sequential

cpog-check: cpog-check.c q25.o
	$(CC) $(CFLAGS) -DTHREADING cpog-check.c q25.o -o cpog-check -lpthread


clean:
	rm -f *~
	rm -f *.o
	rm -rf *.dSYM
	rm -f cpog-check cpog-check-sequential

