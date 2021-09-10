module Main where

 add a b = a + b

-- a {c} b = {a,b,c} = iter c add a b

-- a {1} b = {a,b,1} = a + b
-- a {2} b = {a,b,2} = a * b
-- a {3} b = {a,b,3] = a ^ b

 iter 1 op a b = op a b
 iter (n+1) op a 1 = a
 iter (n+1) op a (b+1) = iter n op a (iter (n+1) op a b)

-- raise = iter 2
 raise op a 1 = a
 raise op a (b+1) = op a (raise op a b)

 rep mop 1 op = op
 rep mop (n+1) op = mop (rep mop n op)

-- iraise = iter
-- iraise 1 op = op
-- iraise (n+1) op = raise (iraise n op)
 
 iraise = rep raise

-- a {{c}} b = {a,b,c,2}

-- a {{1}} b = {a,b,1,2} = a { a { a....a { a { a } a } a.... a } a } a   (b a's from center out)
-- a {{1}} 1 = {a,1,1,2} = a = nest add a 1
-- a {{1}} 2 = {a,2,1,2} = a {a} a = {a,a,a} = iter a add a a = nest add a 2
-- a {{1}} 3 = {a,3,1,2} = a {a {a} a} a = {a,a,{a,a,a}} = iter (iter a add a a) add a a = nest add a 3
-- a {{1}} b = {a,b,1,2} = nest add a b

 nest op a 1 = a
 nest op a (b+1) = iraise (nest op a b) op a a

-- a {{2}} b = a expanded to itself b times (or a multiexpanded to b) = a {{1}} (a {{1}} (a {{1}} (a ....   (b times)
-- a {{2}} b = {a,b,2,2} = iter 2 (nest add) a b
-- a {{3}} b = {a,b,3,2} = iter 3 (nest add) a b
-- a {{c}} b = {a,b,c,2} = iter c (nest add) a b

-- a {{{c}}} b = {a,b,c,3} 

-- a {{{1}}} b = {a,b,1,3} = a {{ a {{ a ... a {{ a {{ a }} a }} a ...  a }} a }} a ( b a's from center out) 
-- a {{{1}}} 1 = {a,1,1,3} = a = nest (nest add) a 1
-- a {{{1}}} 2 = {a,2,1,3} = a {{a}} a = iter a (nest add) a a = nest (nest add) a 2
-- a {{{1}}} 3 = {a,3,1,3} = a {{a {{a}} a}} a = iter (iter a (nest add) a a) (nest add) a a = nest (nest add) a 3
-- a {{{1}}} b = {a,b,1,3} = nest (nest add) a b

-- add = inest 1 add
-- nest add = inest 2 add
-- nest (nest add) = inest 3 add

-- inest 1 op = op 
-- inest (n+1) op = nest (inest n op)
 inest = rep nest 

-- a {1} b     = {a,b,1,1} = inest 1 add a b = a + b
-- a {{1}} b   = {a,b,1,2} = inest 2 add a b
-- a {{{1}}} b = {a,b,1,3} = inest 3 add a b
--               {a,b,1,d} = inest d add a b

-- a {{c}} b = {a,b,c,2} = iter c (nest add) a b = iter c (inest 2 add) a b

-- {a,b,c,d} = iter c (inest d add) a b

-- {a,b,1,1,2} = {a,a,a,{a,b-1,1,1,2}} = a {{{{{{{....{{{a}}}....}}}}}}} a (where there are a {{{{{...{{a}}...}}}}} a angle brackets(where there are a {{{{..{{a}}..}}}} a angle brackets ( where there are .......b times ..... (where there are a angle brackets))))))
-- {a,b,1,1,2} = mnest add a b

 mnest op a 1 = a
 mnest op a (b+1) = iraise a (inest (mnest op a b) op) a a

-- RECAP

-- raise op a 1 = a
-- raise op a (b+1) = op a (raise op a b)
-- nest op a 1 = a
-- nest op a (b+1) = iraise (nest op a b) op a a = rep raise (nest op a b) op a a 
-- mnest op a 1 = a
-- mnest op a (b+1) = iraise a (inest (mnest op a b) add) a a = rep raise a (rep nest (mnest op a b) op) a a 

-- {a,b} = a + b = add a b
-- {a,b,c} = rep raise c add a b
-- {a,b,c,d} = rep raise c (rep nest d add) a b
-- {a,b,1,1,2} = mnest add a b = rep mnest 2 add a b = rep raise 1 (rep nest 1 (rep mnest 2 add)) a b
-- {a,b,c,d,e} = rep raise c (rep nest d (rep mnest e add)) a b

-- raise = xraise 1
-- nest = xraise 2
-- mnest = xraise 3
-- xraise n op a 1 = a
-- xraise 1 op a (b+1) = op a (xraise 1 op a b)
-- xraise 2 op a (b+1) = rep (xraise 1) (xraise 2 op a b) op a a
-- xraise 3 op a (b+1) = rep (xraise 1) a (rep (xraise 2) (xraise 3 op a b) op) a a
-- xraise 4 op a (b+1) = rep (xraise 1) a (rep (xraise 2) a (rep (xraise 3) (xraise 4 op a b) op)) a a ?

-- {a,b,c,d,e} = rep (xraise 1) c (rep (xraise 2) d (rep (xraise 3) e add)) a b

 imnest = rep mnest

 mmnest op a 1 = a
 mmnest op a (b+1) = iraise a (imnest (mmnest op a b) op) a a
-- mmnest op a (b+1) = iraise a (inest (mmnest op a b) op) a a ?

-- xraise 1 = raise
-- xraise 2 = nest
-- xraise 3 = mnest
-- xraise 4 = mmnest

-- let op = add in let a = 2 in let b = 2 in let c = 2 in let d = 2 in let e = 2 in rep (xraise 1) a (rep (xraise 2) a (rep (xraise 3) (xraise 4 op a b) op)) a a
-- 4

-- n -> n+1 :
-- op -> (rep (xraise n) (xraise (n+1) op a b) op)
-- xraise n op a b -> a

 xraise n op a 1 = a
 xraise n op a (b+1) = yraise n op a (xraise n op a b)
 
 yraise 1 op a b = op a b
 yraise (n+1) op a b = yraise n (rep (xraise n) b op) a a

-- xraise 2 add 3 2 = {3,2,1,2} = 3 {{1}} 2 = 3 {3} 3 = 3^3 = 27
-- Main> xraise 2 add 3 2
-- 27

 zraise n op a 1 = a
 zraise 1 op a (b+1) = op a (zraise 1 op a b)
 -- zraise (n+1) op a (b+1) = zraise n (rep (zraise n) b op) a a
 zraise (n+1) op a (b+1) = zraise n (rep (zraise n) (zraise (n+1) op a b) op) a a

