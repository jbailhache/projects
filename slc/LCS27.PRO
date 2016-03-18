
code = 3000

trace 

DOMAINS
	TERM =  i ; k ; s ; z ; e ; ehyp ;  
		symb(SYMBOL) ;    
		var(SYMBOL) ;
		abr(SYMBOL) ;
		ap(TERM,TERM)
	
	PROP =  eq(TERM,TERM) ;
		pt(SYMBOL,PROP) ;
		si(PROP,PROP) ;
		hyp(PROP,PROP) ;
		vrai ; faux ;
		non(PROP) ;
		hypnon(PROP) ;
		et(PROP,PROP) 					
	
	RULE = 	ei ; ek ; es ; ez ; ee ; eehyp ;
		ex(TERM) ; refl(TERM) ; 
		mp ; ai ; as ; 
		loi(SYMBOL) ;
	      	esymb(SYMBOL) ; evar(SYMBOL) ;
	      	sym(DEM) ; trans(DEM,DEM) ;
	      	egap(DEM,DEM) ; 		
	      	di(DEM) ; dk(DEM,DEM) ; ds(DEM,DEM,DEM) ; 
	      	abst(SYMBOL,DEM)	
	      
	DEM = dem(PROP,RULE)      
	
PREDICATES 
	verif(DEM)
	dem(PROP,RULE)	
	equal(TERM,TERM)
	abstract(SYMBOL,TERM,TERM)
	oc(SYMBOL,TERM)
	formint(PROP,PROP)
	formint_term(TERM,TERM)
	atom(TERM)
	absteq(SYMBOL,PROP,PROP)
			
CLAUSES
	equal(X,X).
	
	atom(i).
	atom(k).
	atom(s).
	atom(z).
	atom(e).
	atom(ehyp).
	atom(symb(_)).
/*	atom(var(_)). */
	atom(abr(_)).	

	dem(E,D) :- verif(dem(E,D)).
	dem(P,D) :- formint(P,E), !, dem(E,D), !. 

	verif (dem(eq(i,i), ei)) :- !.
	verif (dem(eq(k,k), ek)) :- !.
	verif (dem(eq(s,s), es)) :- !.
	verif (dem(eq(z,z), ez)) :- !.
	verif (dem(eq(e,e), ee)) :- !.
	verif (dem(eq(ehyp,ehyp), eehyp)) :- !.
	verif (dem(eq(symb(X),symb(X)),esymb(X))) :- !.
	verif (dem(eq(var(X),var(X)),evar(X))) :- !.

	verif (dem(eq(X,X),ex(X))) :- atom(X).
	verif (dem(eq(X,X),refl(X))).
	verif (dem(eq(ap(k,i),ap(ap(s,e),i)), mp)) :- !.
/*	verif (dem(eq(ap(ap(s,ap(ap(s,ap(k,s)),ehyp)),k),
		      ap(ap(s,ap(ap(s,ap(k,s)),ehyp)),ap(k,i))),
		   ai)) :- !.   
*/
	verif (dem(eq(X,Y),ai)) :-
		equal(X,ap(ap(s,ap(ap(s,ap(k,s)),ehyp)),k)),
		equal(Y,ap(ap(s,ap(ap(s,ap(k,s)),ehyp)),ap(k,i))),
		!.
		            
/*
	pour tout a b f x :
		hyp a b f (hyp a b x) = hyp a b (f x)
	lambda a b f x : hyp a b f (hyp a b x)
	= lambda a b f x : hyp a b (f x)
*/
	verif (dem(E,as)) :-
		formint (pt(a,pt(b,pt(f,pt(x, eq(U,V))))), E),
		U = ap(ap(ap(ap(ehyp,var(a)),var(b)),var(f)),
			ap(ap(ap(ehyp,var(a)),var(b)),var(x))),
		V = ap(ap(ap(ehyp,var(a)),var(b)),ap(var(f),var(x))).

	verif (dem(eq(A,B),sym(dem(eq(B,A),R)))) :-
		verif (dem(eq(B,A), R)).
	verif (dem (eq(A,C), trans(dem(eq(A,B),RAB),dem(eq(B,C),RBC)))) :-
		verif (dem(eq(A,B),RAB)),
		verif (dem(eq(B,C),RBC)).
	verif (dem(eq(ap(F,A),ap(G,B)), egap(dem(eq(F,G),RFG),dem(eq(A,B),RAB)))) :-
		verif (dem(eq(F,G),RFG)),
		verif (dem(eq(A,B),RAB)).
	
	verif (dem(eq(A,ap(i,A)),di(dem(eq(A,A),R)))) :- !,
		verif (dem(eq(A,A), R)).
	verif (dem(eq(A,ap(ap(k,A),B)),
		   dk(dem(eq(A,A),RA),dem(eq(B,B),RB)))) :- !,
		verif (dem(eq(A,A), RA)),
		verif (dem(eq(B,B), RB)).
	verif (dem(eq(ap(ap(A,C),ap(B,C)),ap(ap(ap(s,A),B),C)),
		   ds(dem(eq(A,A),RA),dem(eq(B,B),RB),dem(eq(C,C),RC)))) :- !,
		verif (dem(eq(A,A), RA)),
		verif (dem(eq(B,B), RB)),
		verif (dem(eq(C,C), RC)).

	verif (dem(eq(A,B),abst(X,dem(eq(AX,BX),R)))) :-
		verif (dem(eq(AX,BX),R)),
		abstract(X,AX,A),
		abstract(X,BX,B).

	abstract(X,var(X),i).	
	abstract(X,Y,ap(k,Y)) :- bound(X),
				 not(oc(X,Y)).
/*
	abstract(_,i,ap(k,i)).
	abstract(_,k,ap(k,k)).
	abstract(_,s,ap(k,s)).
	abstract(_,z,ap(k,z)).
	abstract(_,e,ap(k,e)).
	abstract(_,ehyp,ap(k,ehyp)).
*/
	abstract(_,X,ap(k,X)) :- atom(X).
	abstract(X,ap(F,var(X)),F) :- 
		not(oc(X,F)).
	abstract(X,ap(F,A),ap(ap(s,LXF),LXA)) :-
		abstract(X,F,LXF),
		abstract(X,A,LXA).
		
	oc(X,var(X)).
	oc(X,ap(F,_)) :- oc(X,F).
	oc(X,ap(_,A)) :- oc(X,A).

	absteq(X,eq(A,B),eq(LXA,LXB)) :-
		abstract(X,A,LXA),
		abstract(X,B,LXB).

	formint_term(X,X) :- atom(X).
	formint_term(ap(F,A),ap(G,B)) :-
		formint_term(F,A),
		formint_term(G,B).
	formint_term(A,C) :-
		formint_term(A,B),
		formint_term(B,C).

	formint_term (abr(a), ap(ap(s,i),i)).
	formint_term (abr(y), ap(abr(a),ap(ap(s,ap(k,ap(s,i))),abr(a)))).
	
			
	formint (eq(A,B), eq(A,B)).

/*
	formint (P, eq(A,B)) :-
		formint (P, eq(C,D)),
		formint_term(C,A),
		formint_term(D,B).
*/	
	formint (pt(X,eq(A,B)), eq(LXA,LXB)) :-
		abstract(X,A,LXA),
		abstract(X,B,LXB).
/*	
	formint (si(eq(A,B),eq(C,D)), 
		 eq(ap(ap(e,A),C),
		    ap(ap(e,B),D))).
		    
	formint (hyp(eq(A,B),eq(C,D)),
		 eq(ap(ap(ehyp,A),C),
		    ap(ap(ehyp,B),D))).
*/
	formint (si(P,Q), eq(ap(ap(e,A),C),
			     ap(ap(e,B),D))) :-
		formint (P, eq(A,B)),
		formint (Q, eq(C,D)).	

	formint (hyp(P,Q), eq(ap(ap(ehyp,A),C),
			      ap(ap(ehyp,B),D))) :-
		formint (P, eq(A,B)),
		formint (Q, eq(C,D)).	

	formint (vrai, eq(i,i)).
	formint (faux, eq(k,ap(k,i))).
	
	formint (non(P), E) :-
		formint (si(P,faux), E).
	formint (hypnon(P), E) :-
		formint (hyp(P,faux), E).
	
	formint (et(P,Q), 
		 eq ( ap(ap(s,ap(ap(s,i),ap(k,A))),ap(k,C)),
		      ap(ap(s,ap(ap(s,i),ap(k,B))),ap(k,D)) )) :-
		formint (P, eq(A,B)),
		formint (Q, eq(C,D)).
/*
	dem(E,D) :- verif(dem(E,D)).
	dem(P,D) :- formint(P,E), !, dem(E,D). 
		
PREDICATES
	def_loi (SYMBOL, PROP)
CLAUSES
	def_loi (N, L) :-
		formint (L, E),
		/* assert (verif(dem(E,loi(N)))). */
		/* D = dem(E,loi(N)), 
		   assert (verif(D)).
		*/
		V = verif (dem(E,loi(N))),
		assert (V).

	verif(dem(E,loi(n))) :- formint(l,E).
	dem(E,loi(n)) 
*/		

PREDICATES
	testabst
CLAUSES
	testabst :- 
		dem (eq(i,i),
			abst (x, dem(eq(var(x),var(x)),
					evar(x)))).
						
PREDICATES
	test
CLAUSES					
	test :- verif(dem(eq(i,ap(i,i)),
			di(dem(eq(i,i),ei)))).

/*
GOAL
	test.
*/

PREDICATES
	toplevel
CLAUSES
	toplevel :- write("Dem ? "),
		    readterm(DEM,dem(E,R)),
		    dem(E,R),
		    D = dem(E,R),
		    write(D).

/*						
DOMAINS
	ITEM = atom(SYMBOL) ; pair(ITEM,ITEM)
	LIST = ITEM*

PREDICATES
	caten(LIST,LIST,LIST)
	
CLAUSES
	caten([],L,L).
	caten([X|A],B,[X|C]):-caten(A,B,C).
*/	