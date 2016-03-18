module ordin where

 data Nat : Set where
  O : Nat
  1+ : Nat -> Nat

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

 rpt : (t : Set) -> Nat -> (t -> t) -> t -> t
 rpt t O f x = x
 rpt t (1+ n) f x = rpt t n f (f x)

 w : Ord -- H suc 0
 -- w = Lim (rep _ Suc Zero)
 w = Lim (\n -> rpt _ n Suc Zero)

 +1 : Ord -> Ord
 +1 x = Suc x

 +w : Ord -> Ord -- H suc
 -- +w x = Lim (rep _ Suc x)
 +w x = Lim (\n -> rpt _ n Suc x)

 +w**2 : Ord -> Ord -- H (H suc)
 -- +w**2 x = Lim (rep _ +w x)
 +w**2 x = Lim (\n -> rpt _ n +w x)

 -- +w**3 : Ord -> Ord
 -- +w**3 x = Lim (rep _ +w**2 x)

 f0 : Ord -> Ord
 f0 = Suc

 f+ : (Ord -> Ord) -> Ord -> Ord
 -- f+ f x = Lim (rep _ f x) 
 f+ f x = Lim (\n -> rpt _ n f x)

 fw : Ord -> Ord
 -- fw x = Lim (\n -> rep _ f+ f0 n x)
 fw x = Lim (\n -> rpt _ n f+ f0 x)

 +w**w : Ord -> Ord -- = fw = w***2 = H H suc
 -- +w**w y = Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) Suc n y)
 +w**w y = Lim (\n -> rpt _ n (\f -> \x -> Lim (\n -> rpt _ n f x)) Suc y)

 +w**<w*2> : Ord -> Ord
 +w**<w*2> y = Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) +w**w n y)

 g0 : Ord -> Ord
 g0 = Suc

 g+ : (Ord -> Ord) -> Ord -> Ord
 -- g+ g y = Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) g n y)
 g+ g y = Lim (\n -> rpt _ n (\f -> \x -> Lim (\n -> rpt _ n f x)) g y)

 gw : Ord -> Ord
 -- gw x = Lim (\n -> rep _ g+ g0 n x)
 gw x = Lim (\n -> rpt _ n g+ g0 x)

 +w**w**2 : Ord -> Ord
 -- +w**w**2 x = Lim (\n -> rep _ (\g -> \y -> Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) g n y)) Suc n x)
 -- +w**w**2 = (\f -> \x -> Lim (\n -> rep _ (\f -> \x -> Lim (\n -> rep _ f+ f n x)) f n x)) Suc
 +w**w**2 = (\f -> \x -> Lim (\n -> rpt _ n (\f -> \x -> Lim (\n -> rpt _ n f+ f x)) f x)) Suc

 h0 = f+
 
 h+ : ford (1+ (1+ (1+ O)))
 -- h+ h = \f -> \x -> Lim (\n -> rep _ h f n x)
 h+ h = \f -> \x -> Lim (\n -> rpt _ n h f x)

 hw : ford (1+ (1+ O))
 -- hw f x = Lim (\n -> rep _ h+ h0 n f x)
 hw f x = Lim (\n -> rpt _ n h+ h0 f x)

 +w***3 : Ord -> Ord
 +w***3 = hw Suc 
 -- +w***3 = (\f -> \x -> Lim (\n -> rep _ (\h -> \f -> \x -> Lim (\n -> rep _ h f n x)) (\f -> \x -> Lim (rep _ f x)) n f x)) Suc 

{-
 +w***0 = +1 = Suc
 +w***1 = +w = \x -> Lim (rep _ suc x)
             = (\f -> \x -> Lim (rep _ f x)) Suc 
             = f+ Suc = h0 Suc
 +w***2      = \x -> Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) Suc n x) 
             = (\f -> \x -> Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) f n x)) Suc
             = \x -> Lim (\n -> rep _ f+ Suc n x)
             = h+ f+ Suc
 +w***3      = hw Suc
             = (\f -> \x -> Lim (\n -> rep _ (\h -> \f -> \x -> Lim (\n -> rep _ h f n x)) (\f -> \x -> Lim (rep _ f x)) n f x)) Suc
  
 +w***0 = +1 = Suc
 +w***1 = +w = (\f -> \x -> Lim (rep _ f x)) Suc 
 +w***2      = (\f -> \x -> Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) f n x)) Suc
 +w***3      = (\f -> \x -> Lim (\n -> rep _ 
         (\h -> \f -> \x -> Lim (\n -> rep _ h f n x)) 
               (\f -> \x -> Lim (\n -> rep _ f x n)) n f x)) Suc

 +w***3 = k+ h+ f+ Suc
 f+ f x = Lim (\n -> rpt _ n f x)
 h+ h f x = Lim (\n -> rpt _ n h f x)
 k+ k h f x = Lim (\n -> rpt _ n k h f x)

-}              

 S0 : ford (1+ O)
 S0 = Suc

 S1 : ford (1+ (1+ O))
 S1 f1 x = Lim (\n -> rpt _ n f1 x)

 S2 : ford (1+ (1+ (1+ O)))
 S2 f2 f1 x = Lim (\n -> rpt _ n f2 f1 x)

 S3 : ford (1+ (1+ (1+ (1+ O))))
 S3 f3 f2 f1 x = Lim (\n -> rpt _ n f3 f2 f1 x)

 S4 : ford (1+ (1+ (1+ (1+ (1+ O)))))
 S4 f4 f3 f2 f1 x = Lim (\n -> rpt _ n f4 f3 f2 f1 x)

 +w***4 : Ord -> Ord
 +w***4 = S4 S3 S2 S1 Suc
