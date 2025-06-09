CC=gcc
CXX=g++
OPT=-O2
#OPT=-O0
VLEVEL=2
CFLAGS=-g $(OPT) -Wno-nullability-completeness
CPPFLAGS=-g $(OPT) -Wno-nullability-completeness -std=c++11

all:  cpog-generate

ilist.o: ilist.c ilist.h
	$(CC) $(CFLAGS) -c ilist.c

report.o: report.c report.h
	$(CC) $(CFLAGS) -c report.c -DVLEVEL=$(VLEVEL)

counters.o: counters.c counters.h
	$(CC) $(CFLAGS) -c counters.c -DVLEVEL=$(VLEVEL)

clausal.o: ilist.h counters.h clausal.hh writer.hh clausal.cpp
	$(CXX) $(CPPFLAGS) -c clausal.cpp -DVLEVEL=$(VLEVEL)

cnf_opt.o: clausal.hh cnf_opt.hh cnf_opt.cpp
	$(CXX) $(CPPFLAGS) -c cnf_opt.cpp -DVLEVEL=$(VLEVEL)

writer.o: ilist.h report.h writer.hh writer.cpp
	$(CXX) $(CPPFLAGS) -c writer.cpp -DVLEVEL=$(VLEVEL)

pog.o: pog.hh clausal.hh cnf_opt.hh counters.h pog.cpp
	$(CXX) $(CPPFLAGS) -c pog.cpp -DVLEVEL=$(VLEVEL)

cpog-generate: cpog-generate.cpp clausal.o cnf_opt.o ilist.o report.o counters.o writer.o pog.o
	$(CXX) $(CPPFLAGS) -o cpog-generate cpog-generate.cpp clausal.o cnf_opt.o ilist.o report.o counters.o writer.o pog.o -DVLEVEL=$(VLEVEL)


.SUFFIXES: .c .cpp .o

.c.o:
	$(CC) $(CFLAGS) $(INC) -DVLEVEL=$(VLEVEL) -c $<

.cpp.o:
	$(CXX) $(CPPFLAGS) $(INC) -DVLEVEL=$(VLEVEL) -c $<

clean:
	rm -f *.o *~
	rm -rf *.dSYM
	rm -f cpog-generate


