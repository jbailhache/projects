SCL : Symbolic Combinatory Logic

SCL is a logical formalism based on combinatory logic and lambda calculus.
This archive contains a program for building proofs in this formalism.
This program interactively reads expressions and displays the result. It can also be used with inpout and output files by redirecting the input and the output.
It has been tested on a PC running Ubuntu and Windows (in a DOS terminal), but it can probably be built on many other systems.
The sources are :
- SCL-DOS.C for the DOS version, which can be compiled with Turbo C for example
- scl-linux.c for the Linux version
In fact the files are almost the same except that Linux needs a filename in lowercase, and  Turbo C needs a filename in uppercase and a source file ending with a ctrl-Z character.
Most of the other files are previous versions or other variants of this program.

THE FORMALISM OF SCL

There is only one kind of objects, which can represent either terms or equalities. The term x is identified with the equality x=x.

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

// is a rule combining transitivity and symmetry which can be expressed by : 
if a = c and b = c, then a = b
Example :
? // # a c # b c
 //#a c #b c  : a  = b

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

Example : proof of SKK=I

- Under Linux : ./scl-linux <skk.scl

- Under DOS : scl-dos <skk.scl

- Interactive session (after typing ./scl-linux under Linux or scl-dos under DOS)

? :I \0
 I  : I  = I  
? :K \\1
 K  : K  = K  
? :S \\\--2 0 -1 0
 S  : S  = S  
? I
 I  : I  = I  
? K
 K  : K  = K  
? S
 S  : S  = S  
? -I a
 -I a  : -I a  = a  
? --K a b
 --K a b  : --K a b  = a  
? ---S a b c
 ---S a b c  : ---S a b c  = --a c -b c  
? $--S K K
 -// %\\--2 0 -1 0 K // \I \\--K 0 -1 0 K  : --S K K  = I  







