SLC : Symbolic Lambda Calculus

SLC is a logical formalism based on lambda calculus and combinatory logic.
This archive contains a program for building proofs in this formalism.
This program interactively reads expressions and displays the result. It can also be used with inpout and output files by redirecting the input and the output.
It has been tested on a PC running Ubuntu and Windows (in a DOS terminal), but it can probably be built on many other systems.
The source is slc.c.
Most of the other files are previous versions or other variants of this program.

THE FORMALISM OF SLC

There is only one kind of objects, which can represent either terms, equalities or proofs. The term x is identified with the equality x=x.

The program interactively reads an expression and displays a representation of the corresponding object followed by an equality of the left and right parts of it considered as an equality.

It uses de Bruijn's notation and classical lambda calculus notation.

A term can be given a name with the folloging syntax :
: name definition
The objects can be combined by different operators :

# a b : an axiom saying that a = b 
Example :
? # a b
 #a b  : a  = b

- a b : application of a to b
Example :
? - # f g # a b
 -#f g #a b  : -f a  = -g b
It means that if f=g and a=b then -f a (the application of f to a) = -g b

// or /> is a rule combining transitivity and symmetry which can be expressed by : 
if a = c and b = c, then a = b
Example :
? // # a c # b c
 //#a c #b c  : a  = b

/< is a similar but symmetrical rule which can be expressed by : 
if a = b and a = c, then b = c
Example :
? /< # a b # a c
 /< #a b #a c  : b  = c

\ a : de Bruijn's abstraction of a
Example ( Schonfinkel's combinator I) :
? \0
 \0  : \0  = \0

% a b : substitutes in a represented with de Bruijn's notation the first variable (0) by b
Variables are represented by 0, 1, 2, ...
Example :
? % 0 a
 %0 a  : -\0 a  = a

_ f a : application of f (a function in de Bruijn's notation) to a with substitution
Example :
? _ \0 a 
 -\0 a  : -\0 a  = a

^x a : Church's abstraction (classical lambda calculus) of variable x from term a
Example (again the combinator I) :
? ^x x
 \0  : \0  = \0

< a : left part of a considered as an equality
Example :
? < # a b
 a  : a  = a

> a : right part of a considered an an equality
Example :
? > # a b
 b  : b  = b

$ a : reduction of a
Example : 
? $ -\0 x
 %0 x  : -\0 x  = x

&$ a : substitutuin in left and right parts of a


Example : proof of SKK=I

- Under Linux : ./scl-linux <skk.slc

- Under DOS : scl-dos <skk.slc

- Interactive session (after typing ./scl-linux under Linux or scl-dos under DOS)

? :I ^a a
 I  : I  = I  
? :K ^a ^b a
 K  : K  = K  
? :S ^a ^b ^c --a c -b c
 S  : S  = S  
? -I a
 -I a  : -I a  = a  
? --K a b
 --K a b  : --K a b  = a  
? ---S a b c
 ---S a b c  : ---S a b c  = --a c -b c  
? $--S K K
 -// %\\--2 0 -1 0 K // \I \\--K 0 -1 0 K  : --S K K  = I  

The file skk-db.slc contains a variant with De Bruijn's notation.

The truth of a proposition p can be represented by its equality with thr combinator I (= \0 = ^a a) : p = I. Then the implication p => q can be represented by the equality -p q = I (with -p q = application of p to q) : if p is true, then p = I, so -p q = q, then q = I which means that q is true. This is illustrated by the following example (file gp.slc) :
Also note that ^ can represent either lambda abstraction or universal quantification.

:true \0
:rule1 ^x ^y ^z # ---parent x y ---parent y z --gdparent x z true
:axiom1 # --parent Allan Brenda true
:axiom2 # --parent Brenda Charles true
:lemma1 &$ ---rule1 Allan Brenda Charles 
:lemma2 - axiom1 ---parent Brenda Charles --gdparent Allan Charles
:lemma3 /< lemma2 lemma1
:lemma4 - axiom2 --gdparent Allan Charles
:theorem1 /< lemma4 lemma3

and here is the corresponding output :

?  true  : true  = true  
?  rule1  : \\\---parent 2 1 ---parent 1 0 --gdparent 2 0  = \\\true  
?  axiom1  : --parent Allan Brenda  = true  
?  axiom2  : --parent Brenda Charles  = true  
?  lemma1  : ---parent Allan Brenda ---parent Brenda Charles --gdparent Allan Charles  = true  
?  lemma2  : ---parent Allan Brenda ---parent Brenda Charles --gdparent Allan Charles  = ---parent Brenda Charles --gdparent Allan Charles  
?  lemma3  : ---parent Brenda Charles --gdparent Allan Charles  = true  
?  lemma4  : ---parent Brenda Charles --gdparent Allan Charles  = --gdparent Allan Charles  
?  theorem1  : --gdparent Allan Charles  = true  
? 






