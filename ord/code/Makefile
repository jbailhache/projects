FILES= \
	README \
	Makefile \
        amenities.agda \
	naturals.agda \
	subset.agda \
	nextU.agda \
	fam.agda \
	predicates.agda \
	ae.agda \
	limit_structure.agda \
	ts.agda \
	acc.agda \
        min.agda \
	ordinals.agda \
	ordlens.agda \
	epsilon0.agda \
	univs.agda

PRINTFILES= \
        amenities.agda \
	naturals.agda \
	subset.agda \
	nextU.agda \
	predicates.agda \
	limit_structure.agda \
	ts.agda \
	min.agda \
	fam.agda \
	ordinals.agda \
	ordlens.agda \
	epsilon0.agda \
	univs.agda

code.tar.gz:	${FILES}
	tar czvf code.tar.gz ${FILES}

test: 
	tar tzvf code.tar.gz

chalmers: code.tar.gz
	rsync -v code.tar.gz pgh@lips.cs.chalmers.se:~pgh/code/ ; \
	ssh pgh@lips.cs.chalmers.se "cd code ; gzip -dc code.tar.gz | tar xvf - "
#	ssh pgh@lips.cs.chalmers.se "cd code ; rm ord.agda* ordlens.agda*"
	date > chalmers

install: code.tar.gz 
	cat code.tar.gz    | cpif ~/www/code.tgz

print: ${PRINTFILES}
	a2ps -1 ${PRINTFILES} -o print.ps
	date > print


