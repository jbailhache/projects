module Bfbwpt where

 -- Taranovsky's Built-from-below with Passthrough notation
 data Ordinal = O | C Ordinal Ordinal Ordinal
  deriving (Eq, Show)

 -- Comparison
 instance Ord Ordinal where
  compare O O = EQ
  compare O _ = LT
  compare _ O = GT
  compare (C a b c) (C d e f) 
   | C a b c <= f = LT
   | c >= C d e f = GT
   | a < d = LT
   | a > d = GT
   | b < e = LT
   | b > e = GT
   | otherwise = EQ
  
 -- List of subterms
 subterms O = [ O ]
 subterms (C a b c) = [ C a b c ] ++ subterms a ++ subterms b ++ subterms c

 -- is_subterm a b : a is subterm of b
 is_subterm O O = True
 is_subterm _ O = False
 is_subterm x (C a b c) = 
  x == C a b c ||
  is_subterm x a ||
  is_subterm x b ||
  is_subterm x c

 -- Standard form
 standard O = True
 standard (C a b c) =
  standard a &&
  standard b &&
  standard c &&
  (case c of
    O -> True
    C d e f -> [a,b] <= [d,e]) &&
  let stb = subterms b in
   flip all stb (\x -> 
    x <= b ||
    flip any stb (\y -> is_subterm x y &&
     y < C a b c ||
     (y /= x &&
      (case y of
        O -> False
        C u v w -> u < a) && 
      flip all stb (\z->
       not (is_subterm x z && is_subterm z y) || z >= y ) ) ) )

 -- list_l l = list of ordinals with l C's in their representation
 list_l 0 = [ O ]
 list_l k1 = let k = k1-1 in
  concat (flip map [0..k] (\l ->
   concat (flip map [0..k-l] (\m ->
    concat (flip map (list_l l) (\d ->
     concat (flip map (list_l m) (\e ->
      concat (flip map (list_l (k-l-m)) (\f ->
       [ C d e f ] )) )) )) )) )) 

 -- Fundamental sequence : fs a k = a[k]
 fs a k = foldr (\x -> \y -> if (x <= y) then y else x) O
           (flip filter (list_l k) (\b -> (standard b) && (b < a)))

 main = print (fs (C O (C O O O) O) 3)

