module Main where

 -- Definition of ordinals in Taranovsky Ordinal Notation 
 data Ton = O | W | C Ton Ton
  deriving (Eq, Show)

 -- Item of postfix representation
 data PostfixItem = CP | OP | WP
  deriving (Eq, Show, Ord)

 -- Convert to postscript representation
 postfix O = [ OP ]
 postfix W = [ WP ]
 postfix (C a b) = postfix b ++ postfix a ++ [ CP ]

 -- short representation of postfix form
 string_postfix [] = ""
 string_postfix (CP:l) = "C" ++ string_postfix l
 string_postfix (OP:l) = "O" ++ string_postfix l
 string_postfix (WP:l) = "W" ++ string_postfix l

 -- Compare ordinals by comparing postfix representations
 instance Ord Ton where
  compare a b = compare (postfix a) (postfix b)

 -- List of subterms of an ordinal
 subterms O = [ O ]
 subterms W = [ W ]
 subterms (C a b) = [ C a b ] ++ subterms a ++ subterms b

 -- bfb n a b : a is n-built from below from b 
 bfb 0 a b = a <= b                    -- a is O-BFB from b if and only if a<b
 bfb n1 a b = let n = n1-1 in          -- a is (n+1)-BFB from b if and only if:
  flip all (subterms a) (\c ->           --  for all subterm c of a,
   c <= a ||                             --   either c <= a
   flip any (subterms a) (\d ->          --   or there exists subterms d of a such that
    elem c (subterms d) && bfb n d b)) --    c is a subterm of d and d is n-BFB from b

 -- standard n a : a is in standard form in n-th system
 standard _ O = True    -- 0 is standard
 standard _ W = True    -- W is standard
 standard n (C a b) =   -- C(a,b) is standard if and only if :
  standard n a &&       --  a is standard
  standard n b &&       --  b is standard
  (case b of            --  b is 0 or W or C(c,d) with a <= c
    O -> True
    W -> True
    C c d -> a <= c) &&
  bfb n a (C a b)     -- a is n-BFB from C(a,b)

 -- Examples
 main = do
  print (standard 0 (C O (C (C O O) O)))
  print (standard 0 (C (C (C O O) O) (C O O)))
  print (standard 0 (C W O))
  print (standard 1 (C W O))
  print (standard 1 (C (C W O) O))
  print (standard 2 (C (C W O) O))


