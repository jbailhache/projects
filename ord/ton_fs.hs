module Ton where

 -- Combinators
 ident x = x
 comp f g x = f (g x)
 swap f x y = f y x

 data Ton 
  = ZeroT
  | Omega
  | C Ton Ton

 instance Eq Ton where
  ZeroT == ZeroT = True
  ZeroT == _ = False
  Omega == Omega = True
  Omega == _ = False
  C a b == C c d = a == c && b == d
  _ == _ = False

 data PostfixItem = CP | ZeroP | OmegaP

 instance Show PostfixItem where
  show CP = "C"
  show ZeroP = "0"
  show OmegaP = "W"

 instance Eq PostfixItem where
  CP == CP = True
  ZeroP == ZeroP = True
  OmegaP == OmegaP = True
  _ == _ = False

 le_item CP _ = True
 le_item ZeroP CP = False
 le_item ZeroP _ = True
 le_item OmegaP OmegaP = True
 le_item OmegaP _ = False

 postfix ZeroT = [ ZeroP ]
 postfix Omega = [ OmegaP ]
 postfix (C a b) = postfix b ++ postfix a ++ [ CP ]

 show_postfix [] = ""
 show_postfix (x:xs) = show x ++ show_postfix xs

 instance Show Ton where
  show a = show_postfix (postfix a)

 le_postfix [] [] = True
 le_postfix [] (_:_) = True
 le_postfix (_:_) [] = False
 le_postfix (a:b) (c:d) = 
  if a == c
  then le_postfix b d
  else le_item a c

 le a b = 
  let pfa = postfix a in
  let pfb = postfix b in 
  le_postfix pfa pfb 

 subterms ZeroT = [ ZeroT ]
 subterms Omega = [ Omega ] 
 subterms (C a b) = [ C a b ] ++ subterms a ++ subterms b

 nbfbf 0 a b = le a b
 nbfbf (n+1) a b = 
  swap all (subterms a) (\c -> 
   le c a || 
   swap any (subterms a) (\d -> 
    elem c (subterms d) && nbfbf n d b)) 

 standard _ ZeroT = True
 standard _ Omega = True
 standard n (C a b) =
  standard n a &&
  standard n b &&
  (case b of
    ZeroT -> True
    Omega -> True
    C c d -> le a c) &&
  nbfbf n a (C a b)

 list_ton_l 0 = [ZeroT, Omega]
 list_ton_l (k+1) = concat (swap map [0..k] (\l -> 
  concat (swap map (list_ton_l l) (\c -> 
   concat (swap map (list_ton_l (k-l)) (\d -> 
    [C c d] )) )) ))

 fs n a k = foldr (\x -> \y -> if (le x y) then y else x) ZeroT
             (swap filter (list_ton_l k) (\b -> (standard n b) && not (le a b)))

