module Main where

 expo b d = b ^ d

 rep f x 0 = x
 rep f x (n+1) = f (rep f x n)

-- E[b]d#r = E[b](E[b](...(E[b]d)...)) repeated r times = rep (expo b) d r
 ebdsr b d r = rep (expo b) d r
-- E[b]d#r1#r2 = E[b]d#(E[b]d#(...(E[b]d#r1)...)) repeated r2 times = rep (rep (expo b) d) r1 r2
-- E[b]d#r1#r2#r3 = E[b]d#r1#(E[b]d#r1#(...(E[b]d#r1#r2)...)) repeated r3 times = rep (rep (rep (expo b) d) r1) r2 r3

-- E[b]d##r = E[b]d#d#...#d with r d's 
-- E[b]d = expo b d
-- E[b]d#d = rep (expo b) d d
-- E[b]d#d#d = rep (rep (expo b) d) d d
-- E[b]d##r = rep (\f -> rep f d) (expo b) r d
 ebdssr b d r = rep (\f -> rep f d) (expo b) r d

-- E[b]d##r1#r2 = E[b]d##(E[b]d##(...(E[b]d##r1)...)) repeated r2 times = rep (\r -> rep (\f -> rep f d) (expo b) r d) r1 r2
-- E[b]d##r1#r2#r3 = E[b]d##r1#(E[b]d##r1#(...(E[b]d##r1#r2)...)) repeated r3 times = rep (rep (\r -> rep (\f -> rep f d) (expo b) r d) r1) r2 r3
-- E[b]d##r1##r2 = E[b]d##r1#r1#r1#...#r1 with r1 repeated r2 times
-- E[b]d##r1 = rep (\f -> rep f d) (expo b) r1 d
-- E[b]d##r1#r1 = rep (\r -> rep (\f -> rep f d) (expo b) r d) r1 r1
-- E[b]d##r1#r1#r1 = rep (rep (\r -> rep (\f -> rep f d) (expo b) r d) r1) r1 r1
-- E[b]d##r1##r2 = rep (\f -> rep f r1) (\r -> rep (\f -> rep f d) (expo b) r d) r2 r1
 ebdssr1ssr2 b d r1 r2 = rep (\f -> rep f r1) (\r -> rep (\f -> rep f d) (expo b) r d) r2 r1
-- E[b]d##r1##r1 = rep (\f -> rep f r1) (\r -> rep (\f -> rep f d) (expo b) r d) r1 r1
-- E[b]d##r1 = rep (\f -> rep f d) (expo b) r1 d
-- E[b]d##r1##r1 = rep (\f -> rep f r1) (\r -> rep (\f -> rep f d) (expo b) r d) r1 r1
 ebdssr1ssr1 b d r1    = rep (\f -> rep f r1) (\r -> rep (\f -> rep f d) (expo b) r d) r1 r1

 ebdssr1ssr1ssr1 b d r1= rep (\f -> rep f r1) (\r -> rep (\f -> rep f d) (\r -> rep (\f -> rep f d) (expo b) r d) r r) r1

-- E[b]d###r1 = E[b]d##r1##r1##...##r1 (r1 times)
 ebdsssr1 b d r1 = rep (\g -> \r -> rep (\f -> rep f d) g r r) (\r -> rep (\f -> rep f d) (expo b) r d) r1 r1

-- ebdsr b d r1 = rep (expo b) d r1
-- ebdssr b d r = rep (\f -> rep f d) (expo b) r1 d
-- ebdsssr1 b d r1 = rep (\g -> \r -> rep (\f -> rep f d) g r r) (\r -> rep (\f -> rep f d) (expo b) r d) r1 r1

