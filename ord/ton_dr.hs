-- Taranovsky Ordinal Notation, system "Degrees of Reflection"

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

 -- nbfbf n a b : a is n-built from below from b 
 nbfbf 0 a b = a <= b                    -- a is O-BFB from b if and only if a<b
 nbfbf n1 a b = let n = n1-1 in          -- a is (n+1)-BFB from b if and only if:
  flip all (subterms a) (\c ->           --  for all subterm c of a,
   c <= a ||                             --   either c <= a
   flip any (subterms a) (\d ->          --   or there exists subterms d of a such that
    elem c (subterms d) && nbfbf n d b)) --    c is a subterm of d and d is n-BFB from b

 cond a b = 
  flip all (subterms a) (\x ->
   flip all (subterms x) (\y ->
    y == x ||
    not (x < y && y < W) ||
    flip any (subterms a) (\z -> 
     elem y (subterms z) &&
     z < W &&
     ((elem x (subterms z) && not (x == z)) || z < C a b) ) ) )

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
  -- nbfbf n a (C a b)     -- a is n-BFB from C(a,b)
  cond a b


 -- list_ton_l l = list of ordinals with l C's in their representation
 list_ton_l 0 = [ O, W ]
 list_ton_l k1 = let k = k1-1 in 
  concat (flip map [0..k] (\l ->
   concat (flip map (list_ton_l l) (\c -> 
    concat (flip map (list_ton_l (k-l)) (\d -> 
     [ C c d ] )) )) ))

 -- fs n a k = k-th element of findamental sequence of a in n-th system
 -- a[k] = max { b | L(b) = k, b is standard and b < a }
 fs n a k = foldr (\x -> \y -> if (x <= y) then y else x) O
             (flip filter (list_ton_l k) (\b -> (standard n b) && (b < a)))

 main = print (fs 1 (C (C O O) O) 3)

