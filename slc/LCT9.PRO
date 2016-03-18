/* Program 9 */
/*
  Goals to enter are on page 40 of the manual.
*/

domains
    row, column, step = integer
    movement = up(step); down(step);
               left(step); right(step); no
    type = o; indefini; f(type,type)
    texpr = i(type); k(type,type); s(type,type,type);
    	ap(texpr,texpr); 
    	y(type);
    	zero; suc; lim
   	rep (texpr, texpr)
   		
predicates
    move_cursor(row,column,movement)
    exprtype (texpr, type)
    e (texpr, texpr)
    
clauses
    exprtype (i(A), f(A,A)).
    exprtype (k(A,B),f(A,f(B,A))).
    exprtype (s(A,B,C), f(f(A,f(B,C)),
    			f(f(A,B),f(A,C)))).
    exprtype (ap(F,X),B) :-
    	/* exprtype (X, A), */
    	/* exprtype (F, f(A,B)), */
    	exprtype (F, C),
    	C = f(A,B),
    	exprtype (X, A).
    	    
    exprtype (y(A), f(f(A,A),A))).
    
    exprtype (zero, o).
    exprtype (suc, f(o,o)).
    exprtype (lim, f(f(o,o),o)).
    
    e(X,X).
    e(X,Y) :- e(Y,X).
    e(X,Z) :- e(X,Y), e(Y,Z).
    e(ap(F,A),ap(G,B)) :- e(F,G), e(A,B).
    
    e(ap(i(T),X),X).
    e(ap(ap(k(A,B),X),Y),X).
    
    move_cursor(R,C,up(Step)):-
        cursor(R,C),
        R1=R-Step,cursor(R1,C).
    move_cursor(R,C,down(Step)):-
        cursor(R,C),
        R1=R+Step,cursor(R1,C).
    move_cursor(R,C,left(Step)):-
        cursor(R,C),
        C1=C-Step,cursor(R,C1).
    move_cursor(R,C,right(Step)):-
        cursor(R,C),
        C1=C+Step,cursor(R,C1).
    move_cursor(R,C,no):-
        cursor(R,C).
