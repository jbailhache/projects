all: lpia
lpia: lpia.o
	cc -o lpia lpia.o
lpia.o: lpia.c
	cc -c -g lpia.c
install: lpia
	cp lpia /usr/bin
