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
    elem c (subterms d) &&  nbfbf n d b)) 

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

 -- Correspondence with "standard" ordinals

 -- power of a function : fpower a f = f^a
 fpower Zero f = ident
 fpower (Suc a) f = comp f (fpower a f)
 fpower (Lim n g) f = \x -> Lim n (\y -> fpower (g y) f x)

 data Ord 
  = Zero
  | Suc Ord
  | Lim Ord (Ord -> Ord)

 h0 f z = Lim Zero (\n -> fpower n f z)

 -- f^n(a)
 iter f Zero a = a
 iter f (Suc b) a = f (iter f b a)
 iter f (Lim k s) a = Lim k (\n -> iter f (s n) a)

 opLim f a = Lim Zero (\n -> f n a)

 opItw f = opLim (iter f)

 -- cardi a = least k with a < W_k
 --           or index of card a
 --           or card a
 -- cardi a = 0 -- todo
 cardi Zero = Zero
 cardi (Suc a) = cardi a
 cardi (Lim k s) = k 

 -- a <= b
 le_ord a b = True -- todo

 -- Taranovsky's C(b,a) = generalization of a + w^b
 tc Zero b = Suc b
 tc (Suc a) b = opItw (tc a) b
 tc (Lim k s) b = 
  if le_ord (cardi (Lim k s)) (cardi b)
  then Lim k (\n -> tc (s n) b)
  else opItw (\x -> tc (s x) b) Zero

 ton_of_ord a = ZeroT -- todo

 ord_of_ton ZeroT = Zero
 ord_of_ton Omega = Lim (Suc Zero) ident
 -- ord_of_ton (C a b) = tc (ord_of_ton a) (ord_of_ton b)
 ord_of_ton (C ZeroT b) = Suc (ord_of_ton b)
 ord_of_ton (C (C ZeroT a) b) = opItw (\x -> ord_of_ton (C a (ton_of_ord x))) (ord_of_ton b)
 
 -- ord_of_ton (C ZeroT b) = Suc (ord_of_ton b)
 -- ord_of_ton (C (Suc a) b) = h0 (C a) b
 -- ord_of_ton (C (C ZeroT a) b) = Lim Zero (\n -> ord_of_ton (fpower n (C a) b))
 -- ord_of_ton (C Omega b) = h0 (\a -> ord_of_ton (C (ton_of_ord a) b)) Zero

  

