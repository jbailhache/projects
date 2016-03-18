/* slc */

code=3000

domains
 file = out
 /* proof (node, level, name, sd1, sd2) */
 /* proof = proof (symbol, integer, symbol, proof, proof) */
 dem = n ; dem(symbol,integer,symbol,dem,dem)
 
 dm = n;
  symb(symbol);
  var(integer);
  axiom(dm,dm);
  ap(dm,dm); 
  /*apsubstr(dm,dm);*/
  ltransym(dm,dm);
  rtransym(dm,dm);
  lambda(dm);
  subst(dm,dm);
  apsubst(dm,dm);
  substlr(dm);
  left(dm);
  right(dm);
  refl(dm);
  llrr(dm)
  
predicates
 shift (integer, integer, dem, dem)
 subst (integer, dem, dem, dem)
 dbname (integer, dem, dem, dem)
 vlambda (dem, dem, dem)
 vl (dm, dm, dm)
 lr (symbol, dem,dem)
 sym (dem, dem)
 trans (dem, dem, dem)
 loopright (dem, dem)
 red (dem, dem)
 red1 (dem, integer, dem)
 red2 (dem, integer, dem)
 red2loop (dem, integer, dem)
 red2loop1 (dem, dem, integer, dem)
 red3 (dem, integer, dem)
 red3ap (dem, dem, integer, dem)
 red3ap1 (dem, dem, integer, dem)
 red3ap2 (dem, integer, dem)
 red3ap3 (dem, dem, dem)
 reduc (dem, integer, dem)
 conv (dm, dem)
 lrdm (symbol, dm, dm)
 lerdm (dm, dm, dm)
 rd (dm, dm)
 outlr (dm, dm)
 test1 (dem)
 testskk (dm, dm)
 testgp (dm, dm)
 parent1 (symbol, symbol)
 gdparent1 (symbol, symbol)
 parent (symbol, symbol, dm)
 gdparent (symbol, symbol, dm)
      
clauses

 conv(n,n).
 conv(symb(S),dem(symb,0,S,n,n)).
 conv(var(N),dem(var,N,n,n,n)).
 conv(axiom(A,B),dem(axiom,0,n,C,D)) :- conv(A,C), conv(B,D).
 conv(ap(A,B),dem(ap,0,n,C,D)) :- conv(A,C), conv(B,D).
 /*conv(apsubstr(A,B),dem(apsubstr,0,n,C,D)) :- conv(A,C), conv(B,D).*/
 conv(ltransym(A,B),dem(ltransym,0,n,C,D)) :- conv(A,C),conv(B,D).
 conv(rtransym(A,B),dem(rtransym,0,n,C,D)) :-conv(A,C),conv(B,D).
 conv(lambda(A),dem(lambda,0,n,B,n)) :- conv(A,B).
 conv(subst(A,B),dem(subst,0,n,C,D)) :- conv(A,C),conv(B,D).
 conv(apsubst(A,B),dem(apsubst,0,n,C,D)) :- conv(A,C),conv(B,D).
 conv(substlr(A),dem(substlr,0,n,B,n)) :- conv(A,B).
 conv(left(A),dem(left,0,n,B,n)) :- conv(A,B).
 conv(right(A),dem(right,0,n,B,n)) :- conv(A,B).
 conv(refl(A),dem(refl,0,n,B,n)) :- conv(A,B).
 conv(llrr(A),dem(llrr,0,n,B,n)) :- conv(A,B).

/*
 shift(M,N,var(N1),var(N2)) if N1 >= M and N2=N+N1.
 shift(M,_,var(N1),var(N1)) if N1 < M.
 shift(M,N,lambda(D1),lambda(D2)) 
  if M1=M+1 and shift(M1,N,D1,D2).
*/
 shift(_,_,n,n) :- !.
 shift(M,N,dem(var,N1,n,n,n),dem(var,N2,n,n,n))
  if N1>=M and ! and N2=N+N1.
 shift(M,_,dem(var,N1,n,n,n),dem(var,N1,n,n,n))
  if ! and N1<M.
 shift(M,N,dem(lambda,0,n,D1,n),dem(lambda,0,n,D2,n))
  if ! and M1=M+1 and shift(M1,N,D1,D2).
 shift(_,_,dem(symb,0,S,n,n),dem(symb,0,S,n,n)) if !.
 shift(M,N,dem(A,B,C,D,E),dem(A,B,C,F,G))
  if shift(M,N,D,F) and shift(M,N,E,G).

 subst(_,n,_,n) :- !.
 subst(N,dem(var,N,n,n,n),Z,Z) :- ! .
 subst(N,dem(var,P,n,n,n),_,dem(var,Q,n,n,n)) :- P>N, !, Q=P-1.
 subst(N,dem(ap,0,n,LY,RY),Z,dem(ap,0,n,LW,RW)) :-
  !, subst(N,LY,Z,LW), subst(N,RY,Z,RW). 
 subst(N,dem(lambda,0,n,Y,n),Z,dem(lambda,0,n,W,n)) :-
  !, N1=N+1, shift(0,1,Z,V), subst(N1,Y,V,W).
 subst(_,dem(symb,0,S,n,n),_,dem(symb,0,S,n,n)) :- !.
 subst(N,dem(K,P,_,L,R),Z,dem(K,P,n,L1,R1)) :-
  subst(N,L,Z,L1), subst(N,R,Z,R1).
  
 dbname(_,_,n,n) :- !.
 dbname(N,X,X,dem(var,N,n,n,n)) :- !.
 dbname(N,X,dem(ap,0,n,L,R),dem(ap,0,n,L1,R1)) :-
  !, dbname(N,X,L,L1), dbname(N,X,R,R1).
 dbname(N,X,dem(lambda,0,n,Y,n),dem(lambda,0,n,Z,n)) :-
  !, N1=N+1, dbname(N1,X,Y,Z).
 dbname(N,X,dem(K,P,S,L,R),dem(K,P,S,L1,R1)) :-
  dbname(N,X,L,L1), dbname(N,X,R,R1).

 vlambda(X,Y,dem(lambda,0,n,Z,n)) :- dbname(0,X,Y,Z).
 vl(X,Y,Z) :- conv(X,A), conv(Y,B), vlambda(A,B,C), conv(Z,C).

 lr(M,dem(ap,0,n,L,R),dem(ap,0,n,L1,R1)) :- !,
  lr(M,L,L1), lr(M,R,R1).
  
 lr(l,dem(ltransym,0,n,X,Y),W) :- !,
  lr(l,X,Z), lr(l,Y,Z), lr(r,X,W).
  
 lr(r,dem(rtransym,0,n,X,Y),W) :- !,
  lr(l,X,Z), lr(l,Y,Z), lr(r,Y,W).
  
 lr(l,dem(rtransym,0,n,X,Y),W) :- !,
  lr(r,X,Z), lr(r,Y,Z), lr(l,X,W).
  
 lr(r,dem(rtransym,0,n,X,Y),W) :- !,
  lr(r,X,Z), lr(r,Y,Z), lr(l,Y,W).
  
 lr(_,dem(symb,0,S,n,n),dem(symb,0,S,n,n)) :- !.
 
 lr(_,dem(var,N,n,n,n),dem(var,N,n,n,n)) :- !.
 
 lr(M,dem(lambda,0,n,X,n),dem(lambda,0,n,Y,n)) :- !,
  lr(M,X,Y).
  
 lr(l,dem(axiom,0,n,X,_),X) :- !.
 lr(r,dem(axiom,0,n,_,X),X) :- !.
 
 lr(l,dem(left,0,n,X,n),dem(left,0,n,Y,n)) :- !, lr(l,X,Y).
 lr(r,dem(left,0,n,X,n),Y) :- !, lr(r,X,Z), lr(l,Z,Y).
 
 lr(l,dem(right,0,n,X,n),dem(right,0,n,Y,n)) :- !, lr(l,X,Y).
 lr(r,dem(right,0,n,X,n),Y) :- !, lr(r,X,Z), lr(r,Z,Y).

 lr(l,dem(subst,0,n,X,Y),dem(ap,0,n,dem(lambda,0,n,X,n),Y)) :- !.
 lr(r,dem(subst,0,n,X,Y),Z) :- !, subst(0,X,Y,Z).  
 
 lr(r,dem(apsubst,0,n,X,Y),W) :-
  lr(r,X,dem(lambda,0,n,Y1,n)), !,
  lr(r,Y,A),
  subst(0,Y1,A,W).
 
 lr(l,dem(apsubst,0,n,X,Y),dem(ap,0,n,S0,S1)) :- !,
  lr(l,X,S0), lr(l,Y,S1).

 lr(l,dem(substlr,0,n,X,n),Y) :-
  lr(l,X,XL),
  lr(l,XL,XL), !,
  lr(r,XL,Y).
 
 lr(r,dem(substlr,0,n,X,n),Y) :-
  lr(l,X,XL),
  lr(l,XL,XL), !,
  lr(r,X,Y).

 lr(_,dem(substlr,0,n,X,n),X) :- !.

 lr(_,dem(refl,0,n,X,n),X) :- !.

 lr(M,dem(llrr,0,n,X,n),Y) :- lr(M,X,Z), lr(M,Z,Y).

 lr(_,X,X).

 lrdm(M,A,B) :- conv(A,C), lr(M,C,D), conv(B,D).
 lerdm(A,B,C) :- lrdm(l,A,B), lrdm(r,A,C).
   
 sym(AB,BA) :- lr(l,AB,AA), BA=dem(ltransym,0,n,AB,AA).    
   
 trans(AB,BC,AC) :-
  sym(AB,BA),
  AC=dem(ltransym,0,n,BA,BC).
   
 loopright(X,X) :- lr(r,X,X), !. 
 loopright(X,Y) :- lr(r,X,Z), loopright(Z,Y).   

 rd(A,B) :- conv(A,C), red(C,D), conv(B,D).
  
 red(X,Y) :- red1(X,1,Y).
 red1(X,A,Y) :- red2(X,A,Y).

 red2(X,RA,R) :-
  red3(X,RA,T1),
  red2loop(T1,RA,R).

 red2loop(T1,RA,T1) :-
  lr(r,T1,T1R),
  red3(T1R,RA,T2),
  lr(l,T2,T2LR),
  lr(r,T2,T2LR), !.

 red2loop(T1,RA,R) :-
  lr(r,T1,T1R),
  red3(T1R,RA,T2),
  trans(T1,T2,T4),
  red2loop1(T1,T4,RA,R).

 red2loop1(T1,T4,RA,R) :-
  lr(l,T4,Y), lr(l,T1,Y), !, 
  red2loop(T4,RA,R).

 red2loop1(T1,_,_,T1).
 
 red3(dem(lambda,0,n,X,n),RA,dem(lambda,0,n,Y,n)) :- !, red1(X,RA,Y).
 red3(dem(ap,0,n,F,A),RA,R) :- !, red3ap(F,A,RA,R).
 red3(X,_,X).
 
 red3ap(dem(lambda,0,n,X,n),A,_,dem(subst,0,n,X,A)) :- !.
 red3ap(dem(ap,0,n,F1,A1),A,RA,R) :- !, red3ap1 (dem(ap,0,n,F1,A1),A,RA,R).
 red3ap(F,A,1,dem(ap,0,n,F,A2)) :- red1(A,1,A2).
 red3ap(F,A,0,dem(ap,0,n,F,A)).

 red3ap1(F,A,1,R) :-
  red1(F,1,F1),
  red1(A,1,A1),
  T3=dem(ap,0,n,F1,A1),
  red3ap2(T3,1,R).
  
 red3ap1(F,A,0,R) :-
  red1(F,1,F1),
  T3=dem(ap,0,n,F1,A),
  red3ap2(T3,0,R).
  
 red3ap2(T3,_,T3) :- lr(l,T3,T3LR), lr(r,T3,T3LR), !. 
 red3ap2(T3,RA,R) :- lr(r,T3,T3R), red1(T3R,RA,T4), red3ap3(T3,T4,R).
 
 red3ap3(T3,T4,T3) :- lr(l,T4,T4LR), lr(r,T4,T4LR), !.
 red3ap3(T3,T4,T) :- trans(T3,T4,T). 
   
 reduc(AB,RA,CD) :-
  lr(l,AB,A),
  lr(r,AB,B),
  red1(A,RA,AC),
  red1(B,RA,BD),
  CB=dem(ltransym,0,n,AC,AB),
  trans(CB,BD,CD).

 outlr(L,R) :-
  openwrite(out,"out.txt"),
  writedevice(out),
  write("L=",L," R=",R),
  closefile(out).
  
 test1(R) :- 
  red(dem(ap,0,n,dem(lambda,0,n,dem(var,0,n,n,n),n),dem(symb,0,a,n,n)),R).
    
 testskk(L,R) :-
  /* vl(symb(a),symb(a),I), */
  vl(symb(b),symb(a),KA),
  vl(symb(a),KA,K),
  vl(symb(c),ap(ap(symb(a),symb(c)),ap(symb(b),symb(c))),SAB),
  vl(symb(b),SAB,SA),
  vl(symb(a),SA,S),
  rd(ap(ap(S,K),K),RSKK),
  lerdm(RSKK,L,R),
  outlr(L,R).

 testgp(L,R) :-
  openwrite(out,"OUT.TXT"),
  writedevice(out),  
  T=lambda(var(0)),
  RXYZ=axiom(ap(ap(ap(symb(parent),symb(x)),symb(y)),ap(ap(ap(symb(parent),symb(y)),symb(z)),
   ap(ap(symb(gdparent),symb(x)),symb(z)))),T),
  write("RXYZ=",RXYZ), nl, 
  vl(symb(z),RXYZ,RXY),
  vl(symb(y),RXY,RX),
  vl(symb(x),RX,R),
  write("R=",R), nl,
  A1=axiom(ap(ap(symb(parent),symb(allan)),symb(brenda)),T),
  write("A1=",A1), nl,
  A2=axiom(ap(ap(symb(parent),symb(brenda)),symb(charles)),T),
  write("A2=",A2), nl,
  L1=substlr(ap(ap(ap(R,symb(allan)),symb(brenda)),symb(charles))),
  write("L1=",L1), nl,
  L2=ap(A1,ap(ap(ap(symb(parent),symb(brenda)),symb(charles)),
   ap(ap(symb(gdparent),symb(allan)),symb(charles)))),
  write("L2=",L2), nl,
  L3=ltransym(L2,L1),
  write("L3=",L3), nl,
  L4=ap(A2,ap(ap(symb(gdparent),symb(allan)),symb(charles))),
  write("L4=",L4), nl,
  T=ltransym(L4,L3),
  write("T=",T), nl,
  lerdm(T,L,R),
  write("L=",L), nl,
  write("R=",R), nl,
  closefile(out).
  
 gdparent1(X,Z) :- parent1(X,Y), parent1(Y,Z).
 parent1(allan,brenda).
 parent1(brenda,charles).

 parent(allan,brenda,axiom(ap(ap(symb(parent),symb(allan)),symb(brenda)),lambda(var(0)))).
 parent(brenda,charles,axiom(ap(ap(symb(parent),symb(brenda)),symb(charles)),lambda(var(0)))).

 gdparent(A,C,T1) :- 
  parent(A,B,A1),
  parent(B,C,A2),
  openwrite(out,"OUT.TXT"),
  writedevice(out),  
  T=lambda(var(0)),
  RXYZ=axiom(ap(ap(ap(symb(parent),symb(x)),symb(y)),ap(ap(ap(symb(parent),symb(y)),symb(z)),
   ap(ap(symb(gdparent),symb(x)),symb(z)))),T),
  write("RXYZ=",RXYZ), nl, 
  vl(symb(z),RXYZ,RXY),
  vl(symb(y),RXY,RX),
  vl(symb(x),RX,R),
  write("R=",R), nl,
  /* 
  A1=axiom(ap(ap(symb(parent),symb(allan)),symb(brenda)),T), 
  write("A1=",A1), nl,
  A2=axiom(ap(ap(symb(parent),symb(brenda)),symb(charles)),T),
  write("A2=",A2), nl,
  */
  L1=substlr(ap(ap(ap(R,symb(A)),symb(B)),symb(C))),
  write("L1=",L1), nl,
  L2=ap(A1,ap(ap(ap(symb(parent),symb(B)),symb(C)),
   ap(ap(symb(gdparent),symb(A)),symb(C)))),
  write("L2=",L2), nl,
  L3=ltransym(L2,L1),
  write("L3=",L3), nl,
  L4=ap(A2,ap(ap(symb(gdparent),symb(A)),symb(C))),
  write("L4=",L4), nl,
  T1=ltransym(L4,L3),
  write("T1=",T1), nl,
  lerdm(T1,L,R),
  write("L=",L), nl,
  write("R=",R), nl,
  closefile(out).
  


 

