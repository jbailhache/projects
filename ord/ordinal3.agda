module ordinal where

-- Primitive data types

 data Bool : Set where
  true : Bool
  false : Bool

 {-# BUILTIN BOOL Bool #-}
 {-# BUILTIN TRUE true #-}
 {-# BUILTIN FALSE false #-}

 if_then_else_ : {A : Set} -> Bool -> A -> A -> A
 if true then x else y = x
 if false then x else y = y

 _and_ : Bool -> Bool -> Bool
 true and x = x
 false and x = false

 _or_ : Bool -> Bool -> Bool
 true or x = true
 false or x = x

 not : Bool -> Bool
 not true = false
 not false = true

 data Nat : Set where
  O : Nat
  1+ : Nat -> Nat

 {-# BUILTIN NATURAL Nat #-}
 {-# BUILTIN ZERO    O #-}
 {-# BUILTIN SUC     1+ #-}

 _+_ : Nat -> Nat -> Nat
 O + n = n
 1+ n + p = 1+ (n + p)

 _-_ : Nat -> Nat -> Nat
 n - O = n
 O - n = O
 (1+ n) - (1+ p) = n - p

 _==_ : Nat -> Nat -> Bool
 O == O = true
 (1+ n) == O = false
 O == (1+ n) = false
 1+ n == 1+ p = n == p
 
 _>=_ : Nat -> Nat -> Bool
 O >= O = true
 O >= 1+ n = false
 1+ n >= O = true
 1+ n >= 1+ p = if n >= p then true else false


 infixr 40 _::_
 data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

 [_] : {A : Set} -> A -> List A
 [ x ] = x :: []

 length : {A : Set} -> List A -> Nat
 length [] = O
 length (x :: l) = 1+ (length l)

 _++_ : {A : Set} -> List A -> List A -> List A
 [] ++ l = l
 (x :: l1) ++ l2 = x :: (l1 ++ l2)

 data Ord : Set where
  Zero : Ord
  Suc : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord

 ford : Nat -> Set
 ford O = Ord
 ford (1+ n) = ford n -> ford n

 OrdOfNat : Nat -> Ord
 OrdOfNat O = Zero
 OrdOfNat (1+ n) = Suc (OrdOfNat n)

{-
 w : Ord
 w = Lim OrdOfNat

 w+1 : Ord
 w+1 = Suc w
-}

 rep : (t : Set) -> (t -> t) -> t -> Nat -> t
 rep t f x O = x
 rep t f x (1+ n) = rep t f (f x) n

 rpt : {t : Set} -> Nat -> (t -> t) -> t -> t
 rpt O f x = x
 rpt (1+ n) f x = rpt n f (f x)


 fix : ford 2
 fix f x = Lim (\n -> rpt n f x)

 H0 = fix

 data Flist (A : Set) (z : A) : Set where
  flist : (Nat -> A) -> Nat -> Flist A z
 
 fncfl : {A : Set} -> {z : A} -> Flist A z -> (Nat -> A)
 fncfl (flist f l) = f

 lenfl : {A : Set} -> {z : A} -> Flist A z -> Nat
 lenfl (flist f l) = l

 nthfl : {A : Set} -> {z : A} -> Flist A z -> Nat -> A
 nthfl fl i = fncfl fl i
  
 data OrdList : Set where
  ordlist : Flist Ord Zero -> OrdList

 lenol : OrdList -> Nat
 lenol (ordlist fl) = lenfl fl

 nthol : OrdList -> Nat -> Ord
 nthol (ordlist fl) i = nthfl fl i
 
 _[_:=_] : OrdList -> Nat -> Ord -> OrdList
 ol [ i := a ] = ordlist (flist (\j -> if j == i then a else nthol ol j) (lenol ol)) 

 ZeroOrdList : Nat -> OrdList
 ZeroOrdList n = ordlist (flist (\i -> Zero) n)

 phi'0 : Ord -> Ord
 phi'0 Zero = Suc Zero
 phi'0 (Suc a) = Suc (phi'0 a)
 phi'0 (Lim f) = Lim (\n -> phi'0 (f n))

 phi'1 : Nat -> OrdList -> Ord
 phi'1 r ol with r >= lenol ol
 phi'1 r ol | true = phi'0 (nthol ol O)
 phi'1 r ol | false with nthol ol (1+ r)
 phi'1 r ol | false | Zero = phi'1 (1+ r) ol
 phi'1 r ol | false | Suc b with nthol ol O
 phi'1 r ol | false | Suc b | Zero  = fix (\x -> phi'1 (r - 1) (ol [ r := x ] [ 1+ r := b ])) Zero
 phi'1 r ol | false | Suc b | Suc a = fix (\x -> phi'1 (r - 1) (ol [ r := x ] [ 1+ r := b ])) (Suc (phi'1 r (ol [ O := a ])))
 phi'1 r ol | false | Suc b | Lim f = Lim (\n -> phi'1 r (ol [ O := f n ]))
 phi'1 r ol | false | Lim f = Lim (\n -> phi'1 r (ol [ 1+ r := f n ]))

 phi' : OrdList -> Ord
 phi' ol = phi'1 O ol

 SmallVeblen = Lim (\n -> phi' (ZeroOrdList (1+ n) [ n := Suc Zero ]))
 

 phi0 : Ord -> Ord
 phi0 Zero = Suc Zero
 phi0 (Suc a) = Suc (phi0 a)
 phi0 (Lim f) = Lim (\n -> phi0 (f n))


 phi : List Ord -> Ord
 phia : Ord -> Nat -> List Ord -> Ord

 phi [] = Suc Zero
 phi (a :: l) = phia a O l

 -- phia a r [] = cantor a Zero
 phia a r [] = phi0 a
 phia a r (Zero :: l) = phia a (1+ r) l
 phia Zero O (Suc b :: l) = H0 (\x -> phia x O (b :: l)) Zero
 phia (Suc a) O (Suc b :: l) = H0 (\x -> phia x O (b :: l)) (Suc (phia a O (Suc b :: l)))
 phia (Lim f) O (Suc b :: l) = Lim (\n -> phia (f n) O (Suc b :: l))
 phia Zero (1+ r) (Suc b :: l) = H0 (\x -> phia Zero r (x :: b :: l)) Zero
 phia (Suc a) (1+ r) (Suc b :: l) = H0 (\x -> phia Zero r (x :: b :: l)) (Suc (phia a (1+ r) (Suc b :: l)))
 phia (Lim f) (1+ r) (Suc b :: l) = Lim (\n -> phia (f n) (1+ r) (Suc b :: l))
 phia a r (Lim f :: l) = Lim (\n -> phia a r ((f n) :: l)) 


 phif : Nat -> (Nat -> Ord) -> Ord
 phib : Nat -> Nat -> (Nat -> Ord) -> Ord
 phic : Nat -> Nat -> (Nat -> Ord) -> Ord -> Ord
 phid : Nat -> Nat -> (Nat -> Ord) -> Ord -> Ord -> Ord

 phif s g = phib O s g

 phib r s g = 
  if r >= s 
  -- then cantor (g O) Zero
  then phi0 (g 0)
  else phic r s g (g (1+ r))

 phic r s g Zero = phib (1+ r) s g
 phic r s g (Suc b) = phid r s g b (g O)
 phic r s g (Lim f) = Lim (\n -> phib O s (\p -> if p == 1+ r then f n else g p))

 phid r s g b Zero    = H0 (\x -> phif s (\p -> if p == r then x else if p == 1+ r then b else g p)) Zero
 phid r s g b (Suc a) = H0 (\x -> phif s (\p -> if p == r then x else if p == 1+ r then b else g p)) 
                        (Suc (phif s (\p -> if p == O then a else g p)))
 phid r s g b (Lim f) = Lim (\n -> phif s (\p -> if p == O then f n else g p))


 phie : Nat -> Nat -> (Nat -> Ord) -> Ord
 phie r s g with r >= s
 -- phie r s g | true = cantor (g O) Zero
 phie r s g | true = phi0 (g O)
 phie r s g | false with g (1+ r)
 phie r s g | false | Zero = phie (1+ r) s g
 phie r s g | false | Suc b with g O
 phie r s g | false | Suc b | Zero  = H0 (\x -> phie O s (\p -> if p == r then x else if p == 1+ r then b else g p)) Zero
 phie r s g | false | Suc b | Suc a = H0 (\x -> phie O s (\p -> if p == r then x else if p == 1+ r then b else g p))
                                      (Suc (phie O s (\p -> if p == O then a else g p)))
 phie r s g | false | Suc b | Lim f = Lim (\n -> phie r s (\p -> if p == O then f n else g p))
 phie r s g | false | Lim f = Lim (\n -> phie r s (\p -> if p == 1+ r then f n else g p))


 SmallVeblen1 = Lim (\n -> phif n (\p -> if 1+ p == n then Suc Zero else Zero))
 
 SmallVeblen2 = Lim (\n -> phie O n (\p -> if 1+ p == n then Suc Zero else Zero))




