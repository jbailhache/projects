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

 rpt : {t : Set} -> Nat -> (t -> t) -> t -> t
 rpt O f x = x
 rpt (1+ n) f x = rpt n f (f x)

 w : Ord -- H suc 0
 -- w = Lim (rep _ Suc Zero)
 w = Lim (\n -> rpt n Suc Zero)

 +1 : Ord -> Ord
 +1 x = Suc x

 +w : Ord -> Ord -- H suc
 -- +w x = Lim (rep _ Suc x)
 +w x = Lim (\n -> rpt n Suc x)

 +w**2 : Ord -> Ord -- H (H suc)
 -- +w**2 x = Lim (rep _ +w x)
 +w**2 x = Lim (\n -> rpt n +w x)

 -- +w**3 : Ord -> Ord
 -- +w**3 x = Lim (rep _ +w**2 x)

 f0 : Ord -> Ord
 f0 = Suc

 f+ : (Ord -> Ord) -> Ord -> Ord
 -- f+ f x = Lim (rep _ f x) 
 f+ f x = Lim (\n -> rpt n f x)

 fw : Ord -> Ord
 -- fw x = Lim (\n -> rep _ f+ f0 n x)
 fw x = Lim (\n -> rpt n f+ f0 x)

 +w**w : Ord -> Ord -- = fw = w***2 = H H suc
 -- +w**w y = Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) Suc n y)
 +w**w y = Lim (\n -> rpt n (\f -> \x -> Lim (\n -> rpt n f x)) Suc y)

 +w**<w*2> : Ord -> Ord
 +w**<w*2> y = Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) +w**w n y)

 g0 : Ord -> Ord
 g0 = Suc

 g+ : (Ord -> Ord) -> Ord -> Ord
 -- g+ g y = Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) g n y)
 g+ g y = Lim (\n -> rpt n (\f -> \x -> Lim (\n -> rpt n f x)) g y)

 gw : Ord -> Ord
 -- gw x = Lim (\n -> rep _ g+ g0 n x)
 gw x = Lim (\n -> rpt n g+ g0 x)

 +w**w**2 : Ord -> Ord
 -- +w**w**2 x = Lim (\n -> rep _ (\g -> \y -> Lim (\n -> rep _ (\f -> \x -> Lim (rep _ f x)) g n y)) Suc n x)
 -- +w**w**2 = (\f -> \x -> Lim (\n -> rep _ (\f -> \x -> Lim (\n -> rep _ f+ f n x)) f n x)) Suc
 +w**w**2 = (\f -> \x -> Lim (\n -> rpt n (\f -> \x -> Lim (\n -> rpt n f+ f x)) f x)) Suc

 h0 = f+
 
 h+ : ford (1+ (1+ (1+ O)))
 -- h+ h = \f -> \x -> Lim (\n -> rep _ h f n x)
 h+ h = \f -> \x -> Lim (\n -> rpt n h f x)

 hw : ford (1+ (1+ O))
 -- hw f x = Lim (\n -> rep _ h+ h0 n f x)
 hw f x = Lim (\n -> rpt n h+ h0 f x)

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
 f+ f x = Lim (\n -> rpt n f x)
 h+ h f x = Lim (\n -> rpt n h f x)
 k+ k h f x = Lim (\n -> rpt n k h f x)

-}              

 -- H0 : ford (1+ O)
 -- H0 = Suc

 H0 : ford (1+ (1+ O))
 H0 f1 x = Lim (\n -> rpt n f1 x)

 H1 : ford (1+ (1+ (1+ O)))
 H1 f2 f1 x = Lim (\n -> rpt n f2 f1 x)

 H2 : ford (1+ (1+ (1+ (1+ O))))
 H2 f3 f2 f1 x = Lim (\n -> rpt n f3 f2 f1 x)

 H3 : ford (1+ (1+ (1+ (1+ (1+ O)))))
 H3 f4 f3 f2 f1 x = Lim (\n -> rpt n f4 f3 f2 f1 x)

 +w***4 : Ord -> Ord
 +w***4 = H3 H2 H1 H0 Suc

 I : {t : Set} -> t -> t
 I x = x

 insert : {s t u : Set} -> s -> (t -> u) -> (s -> t) -> u
 insert x a f = a (f x)

 -- array n f x1 ... xn = f <x1, ..., xn>
 -- array : {s t u v : Set} -> Nat -> (((s -> t) -> u) -> v) -> s -> (s -> t) -> u
 -- array : {t u v : Set} -> Nat -> ((t -> t) -> u -> v) -> u -> v
 -- array O f = f I 
 -- array (1+ n) f x = array n (\a -> f (insert x a))

 array0 : {t  u : Set} -> ((t -> t) -> u) -> u
 array0 f = f I

 array1 : {s t u : Set} -> (((s -> t) -> t) -> u) -> s -> u
 array1 f x = f (\g -> g x)

 array2 : {s1 s2 t u : Set} -> (((s1 -> s2 -> t) -> t) -> u) -> s1 -> s2 -> u
 array2 f x1 x2 = f (\g -> g x1 x2)


 lim1 : (Nat -> ford (1+ O)) -> ford (1+ O)
 lim1 f x = Lim (\n -> f n x)

 lim2 : (Nat -> ford (1+ (1+ O))) -> ford (1+ (1+ O))
 lim2 f x = lim1 (\n -> f n x)

 lim3 : (Nat -> ford (1+ (1+ (1+ O)))) -> ford (1+ (1+ (1+ O)))
 lim3 f x = lim2 (\n -> f n x)

 limn : (n : Nat) -> (Nat -> ford n) -> ford n
 limn O f = Lim f
 limn (1+ p) f = \x -> limn p (\n -> f n x)

 H : (n : Nat) -> ford (1+ (1+ n))
 H n f x = limn n (\n -> rpt n f x)

 H' : {n : Nat} -> ford (1+ (1+ n))
 H' f x = limn _ (\n -> rpt n f x)

 +w***5 : Ord -> Ord
 -- +w***5 = (H (1+ (1+ (1+ (1+ O))))) (H (1+ (1+ (1+ O)))) (H (1+ (1+ O))) (H (1+ O)) (H O) Suc
 +w***5 = (H _) (H _) (H _) (H _) (H _) Suc

 -- Hseq n  = (H _) ... (H _)
 Hseq : {p : Nat} -> Nat -> ford (1+ (1+ p))
 Hseq O = H _
 Hseq (1+ n) = (Hseq n) (H _) 

 Eps0a : Ord
 Eps0a = Lim (\(n : Nat) -> Hseq n Suc Zero)

 seq : {p : Nat} -> (h : (n : Nat) -> ford (1+ (1+ n))) -> (n : Nat) -> ford (1+ (1+ p))
 seq h O = h _
 seq h (1+ n) = seq h n (h _)
 
 Eps0b : Ord
 Eps0b = Lim (\n -> seq H n Suc Zero)

 rp : {p : Nat} -> (n : Nat) -> (h : (n : Nat) -> ford (1+ (1+ n))) -> ford (1+ (1+ p))
 rp O h = h _
 rp (1+ n) h = rp n h (h _)

 Eps0c : Ord
 Eps0c = Lim (\n -> rp n H Suc Zero)

 R10 : ((n : Nat) -> ford (1+ (1+ n))) -> ford (1+ (1+ O)) -- (Ord -> Ord) -> Ord -> Ord
 R10 h s z = Lim (\n -> rp n h s z)

 Eps0d : Ord
 Eps0d = R10 H Suc Zero

 R1 : (p : Nat) -> ((n : Nat) -> ford (1+ (1+ n))) -> ford (1+ (1+ p))
 R1 p h = limn (1+ (1+ p)) (\n -> rp n h)

 Eps0 : Ord
 Eps0 = R1 _ H Suc Zero

 +Eps0 : Ord -> Ord
 +Eps0 = R1 _ H Suc

 R1H : (p : Nat) -> ford (1+ (1+ p))
 R1H p = R1 p H

 -- R1HR1H p : (p : Nat) -> ford (1+ (1+ p))
 -- R1HR1H p s z = R1 _ H (R1 _) H s z 

 rp' : {p : Nat} -> (n : Nat) -> (h : {q : Nat} -> ford (1+ (1+ q))) -> ford (1+ (1+ p))
 rp' O h = h 
 rp' (1+ n) h = rp' n h h

 R'1 : {p : Nat} -> ({n : Nat} -> ford (1+ (1+ n))) -> ford (1+ (1+ p))
 R'1 h = limn _ (\n -> rp' n h)

 Eps0' : Ord
 Eps0' = R'1 H' Suc Zero

 -- HR1HSZ' : Ord
 -- HR1HSZ' = H' R'1 H' Suc Zero

 R1H<R1H>SZ : Ord
 R1H<R1H>SZ = R1 _ H (R1 _ H) Suc Zero

 R1<R1H>SZ : Ord
 R1<R1H>SZ = R1 _ (\n -> R1 n H) Suc Zero

 HR1HSZa : Ord
 HR1HSZa = Lim (\n -> rpt n (\h -> \n -> R1 n h) H O Suc Zero)

 HR1HSZb : Ord
 HR1HSZb = lim2 (\n -> rpt n (\h -> \n -> R1 n h) H O) Suc Zero


 HR1H : (p : Nat) -> ford (1+ (1+ p))
 HR1H p = limn (1+ (1+ p)) (\n -> rpt n (\h -> \n -> R1 n h) H p)

 HR1HSZc : Ord
 HR1HSZc = HR1H _ Suc Zero

 -- R1<HR1H> ?
 HR1<HR1H> : (p : Nat) ->  ford (1+ (1+ p))
 HR1<HR1H> p = limn (1+ (1+ p)) (\n -> rpt n (\h -> \n -> R1 n h) HR1H p)

 HR1<HR1H>SZ : Ord
 HR1<HR1H>SZ = HR1<HR1H> _ Suc Zero

 -- R1<R1<HR1H>> ?
 HR1<HR1<HR1H>> : (p : Nat) -> ford (1+ (1+ p))
 HR1<HR1<HR1H>> p = limn (1+ (1+ p)) (\n -> rpt n (\h -> \n -> R1 n h) HR1<HR1H> p) 

 -- HR1<HR1H> ?
 H<HR1>H : (p : Nat) -> ford (1+ (1+ p))
 H<HR1>H p = limn (1+ (1+ p)) (\q -> rpt q (\f -> \p -> limn (1+ (1+ p)) (\n -> rpt n (\h -> \n -> R1 n h) f p)) H p) 
 -- 0 : H p
 -- 1 : limn _ (\n -> rpt n (\h -> \n -> R1 n h) H p) = HR1H p
 -- w : H<HR1>H p

 -- H<HR1>H ?
 HHR1H : (p : Nat) -> ford (1+ (1+ p))
 -- HHR1H p = limn _ (\q -> rpt q (\F -> \f -> \p -> limn _ (\n -> rpt n F f p)) (\h -> \n -> R1 n h) H p)
 HHR1H = (\G -> \g -> \p -> limn _ (\q -> rpt q 
         (\F -> \f -> \p -> limn _ (\n -> rpt n 
         F f p)) 
         G g p)) 
          (\h -> \n -> R1 n h) H
 
 HHHR1H : (p : Nat) -> ford (1+ (1+ p))
 HHHR1H = (\K -> \k -> \p -> limn _ (\r -> rpt r
          (\G -> \g -> \p -> limn _ (\q -> rpt q 
          (\F -> \f -> \p -> limn _ (\n -> rpt n 
          F f p)) 
          G g p)) 
          K k p))
           (\h -> \n -> R1 n h) H

 R1HR1H : (p : Nat) -> ford (1+ (1+ p))
 -- R1HR1H p = limn _ (\r -> rpt r (\K -> \G -> \g -> \p -> limn _ (\q -> rpt q K G g p)) (\F -> \f -> \p -> limn _ (\n -> rpt n F f p)) (\h -> \n -> R1 n h) H p)
{-
 R1HR1H = (\K1 -> \G1 -> \g1 -> \p -> limn _ (\r -> rpt r 
          (\K  -> \G  -> \g  -> \p -> limn _ (\q -> rpt q 
          K G g p))
          K1 G1 g1 p))
          (\F -> \f -> \p -> limn _ (\n -> rpt n F f p)) (\h -> \n -> R1 n h) H 
-}
 R1HR1H = (\K1 -> \G1 -> \g1 -> \p -> limn _ (\r -> rpt r 
          (\K  -> \G  -> \g  -> \p -> limn _ (\q -> rpt q 
           K G g p))
           K1 G1 g1 p))           
            (\F -> \f -> \p -> limn _ (\n -> rpt n F f p)) -- K1
            (\h -> \n -> limn _ (\n -> rp n h))            -- G1
            (\n -> \f -> \x -> limn _ (\n -> rpt n f x))   -- g1 = H

 R1HR1HR1H : (p : Nat) -> ford (1+ (1+ p))
 R1HR1HR1H = (\K -> \G -> \g -> \p -> limn _ (\q -> rpt q
             (\K -> \G -> \g -> \p -> limn _ (\q -> rpt q
             (\K -> \G -> \g -> \p -> limn _ (\q -> rpt q
              K G g p))
              K G g p))
              K G g p))
               (\F -> \f -> \p -> limn _ (\n -> rpt n F f p)) -- K1
               (\h -> \n -> limn _ (\n -> rp n h))            -- G1
               (\n -> \f -> \x -> limn _ (\n -> rpt n f x))   -- g1 = H    

 R2R1H : (p : Nat) -> ford (1+ (1+ p))
 R2R1H = (\L -> \K -> \G -> \g -> \p -> limn _ (\q -> rpt q
         (\L -> \K -> \G -> \g -> \p -> limn _ (\q -> rpt q 
          L K G g p)) 
          L K G g p)) 
                 (\K -> \G -> \g -> \p -> limn _ (\q -> rpt q K G g p)) -- L
                 (\F -> \f -> \p -> limn _ (\n -> rpt n F f p))         -- K
                 (\h -> \n -> limn _ (\n -> rp n h))                    -- G
                 (\n -> \f -> \x -> limn _ (\n -> rpt n f x))           -- g = H    

 R3R2R1H : (p : Nat) -> ford (1+ (1+ p))
 R3R2R1H = (\L -> \K -> \G -> \g -> \p -> limn _ (\q -> rpt q
           (\L -> \K -> \G -> \g -> \p -> limn _ (\q -> rpt q 
           (\L -> \K -> \G -> \g -> \p -> limn _ (\q -> rpt q 
            L K G g p)) 
            L K G g p)) 
            L K G g p)) 
                 (\K -> \G -> \g -> \p -> limn _ (\q -> rpt q K G g p)) -- L
                 (\F -> \f -> \p -> limn _ (\n -> rpt n F f p))         -- K
                 (\h -> \n -> limn _ (\n -> rp n h))                    -- G
                 (\n -> \f -> \x -> limn _ (\n -> rpt n f x))           -- g = H    

 Rw_1H : (p : Nat) -> ford (1+ (1+ p))
 Rw_1H = (\M -> \L -> \K -> \G -> \g -> \p -> limn _ (\q -> rpt q 
         (\M -> \L -> \K -> \G -> \g -> \p -> limn _ (\q -> rpt q 
          M L K G g p))
          M L K G g p))
                 (\L -> \K -> \G -> \g -> \p -> limn _ (\q -> rpt q L K G g p)) -- M
                 (\K -> \G -> \g -> \p -> limn _ (\q -> rpt q K G g p))         -- L
                 (\F -> \f -> \p -> limn _ (\n -> rpt n F f p))                 -- K
                 (\h -> \n -> limn _ (\n -> rp n h))                            -- G
                 (\n -> \f -> \x -> limn _ (\n -> rpt n f x))                   -- g = H    

 
 -- HHR1HSZ : Ord
 -- HHR1HSZ = Lim (\n -> rpt n (\h -> \n -> H _ R1 n h) H O Suc Zero)

{-
 subst : (Ord -> Ord) -> Ord -> Ord -> Ord
 subst s z Zero = z
 subst s z (Suc x) = s (subst s z x)
 subst s z (Lim f) = Lim (\n -> subst s z (f n))
-}

 subst : Ord -> (Ord -> Ord) -> Ord -> Ord 
 subst Zero s z = z
 subst (Suc x) s z = s (subst x s z)
 subst (Lim f) s z = Lim (\n -> subst (f n) s z)

 substn : {n : Nat} -> Ord -> ford (1+ (1+ n))
 substn Zero s z = z
 substn (Suc x) s z = s (substn x s z)
 substn (Lim f) s z = limn _ (\n -> substn (f n) s z)

 -- x0 = Eps0

 ex : ford (1+ (1+ O))
 ex +x = substn (+x Zero) (\f -> \x -> subst (f Zero) f (f x)) +Eps0

 x1 : Ord
 x1 = subst Eps0 +Eps0 Eps0
 -- x1 = subst Eps0 +Eps0 Zero

 +x1 : Ord -> Ord
 -- +x1 x = substn Eps0 +Eps0 (+Eps0 x)
 +x1 = substn (+Eps0 Zero) ex +Eps0

 x2 : Ord
 x2 = subst x1 +x1 x1

 +x2 : Ord -> Ord
 -- +x1 x = subst x0 +x0 (+x0 x)
 +x2 x = subst (+x1 Zero) +x1 (+x1 x)
 -- ou subst (+x1 x) +x1 (+x1 x)

 +xn : Nat -> Ord -> Ord
 +xn O x = +Eps0 x
 +xn (1+ n) x = subst (+xn n Zero) (+xn n) (+xn n x)

 +xw : Ord -> Ord
 -- +xw x = Lim (\n -> +xn n x)
 -- +xw = limn _ (\n -> rpt n (\f -> \x -> subst (f Zero) f (f x)) +Eps0)
 +xw = limn _ (\n -> rpt n (\f -> \x -> substn (f Zero) f (f x)) +x1)

 -- +xEps0 : Ord -> Ord
 -- +xEps0 = subst (+Eps0 Zero) (\f -> \x -> subst (f Zero) f (f x)) +Eps0

 +xEps0 : Ord -> Ord
 -- +xEps0 = substn (+Eps0 Zero) (\f -> \x -> subst (f Zero) f (f x)) +Eps0
 +xEps0 = substn (+Eps0 Zero) (\f -> \x -> subst (f Zero) f (f x)) +x1

 fx : ford (1+ (1+ O))
 fx +x = substn (+x Zero) (\f -> \x -> subst (f Zero) f (f x)) +x1

 +y1 : Ord -> Ord
 +y1 = substn (+Eps0 Zero) fx +Eps0 

 +y2 : Ord -> Ord
 +y2 x = subst (+y1 Zero) +y1 (+y1 x)

 +yw : Ord -> Ord
 +yw = limn _ (\n -> rpt n (\f -> \x -> substn (f Zero) f (f x)) +y1)

 +yEps0 : Ord -> Ord
 +yEps0 = substn (+Eps0 Zero) (\f -> \x -> subst (f Zero) f (f x)) +y1

 -- +x1' : Ord -> Ord
 -- +x1' = substn (+Eps0 Zero) ex +Eps0

 efx : ford (1+ (1+ (1+ O)))
 efx F = \plusx -> substn (plusx Zero) (\f -> \x -> subst (f Zero) f (f x)) (substn (+Eps0 Zero) F +Eps0)
 
 zx : ford (1+ (1+ O))
 zx = substn (+Eps0 Zero) efx ex 

 -- s1 : (Ord -> Ord) -> Ord -> Ord 
 -- s1 f = subst (f Zero) f (f Zero)

 subst1 : {t : Set} -> Ord -> ((t -> Ord) -> t -> Ord) -> (t -> Ord) -> t -> Ord
 subst1 Zero s z a  = z a 
 subst1 (Suc x) s z a = s (subst1 x s z) a
 subst1 (Lim f) s z a = Lim (\n -> subst1 (f n) s z a) 

 subst2 : {t1 t2 : Set} -> Ord -> ((t1 -> t2 -> Ord) -> t1 -> t2 -> Ord) -> (t1 -> t2 -> Ord) -> t1 -> t2 -> Ord
 subst2 Zero s z a1 a2 = z a1 a2 
 subst2 (Suc x) s z a1 a2 = s (subst2 x s z) a1 a2
 subst2 (Lim f) s z a1 a2 = Lim (\n -> subst2 (f n) s z a1 a2) 

 a0 : Ord
 a0 = w

 a1 : Ord -> Ord
 a1 = +w

 b2 : Ord -> ford (1+ (1+ O))
 b2 Zero f y = f y
 b2 (Suc x) f y = substn y (b2 x f) y
 b2 (Lim phi) f y = Lim (\n -> b2 (phi n) f y)
 -- b2 (Lim phi) f y = limn _ (\n -> b2 (phi n) f y)

 a2 : ford (1+ (1+ O))
 a2 f x = b2 x f x

 b3 : Ord -> ford (1+ (1+ (1+ O)))
 b3 Zero g f y = g f y
 b3 (Suc x) g f y = substn y (b3 x g) f y
 b3 (Lim phi) g f y = Lim (\n -> b3 (phi n) g f y)

 a3 : ford (1+ (1+ (1+ O)))
 a3 g f x = b3 x g f x

 b4 : Ord -> ford (1+ (1+ (1+ (1+ O))))
 b4 Zero h g f y = h g f y
 b4 (Suc x) h g f y = substn y (b4 x h) g f y
 b4 (Lim phi) h g f y = Lim (\n -> b4 (phi n) h g f y)

{-
 b4 : {t : Set} -> ((t -> Ord -> Ord) -> t -> Ord -> Ord) -> Ord -> (t -> Ord -> Ord) -> t -> Ord -> Ord
 b4 p Zero m f x = p m f x
 b4 p (Suc n) m f x = META2 _ _ (b4 p n) m x f x
 b4 p (Lim phi) m f x = Lim (\(y : Nat) -> b4 p (phi y) m f x)
-}

 -- I : {s : Set} -> s -> s
 -- I a = a

 K : {s t : Set} -> s -> t -> s
 K a b = a

 S : {s t u : Set} -> (s -> t -> u) -> (s -> t) -> (s -> u)
 S a b c = a c (b c)

 C : {s t u : Set} -> (s -> t -> u) -> (t -> s -> u) 
 C a b c = a c b

 B : {s t u : Set} -> (s -> t) -> (u -> s) -> (u -> t)
 B a b c = a (b c)

 W : {s t u : Set} -> (s -> s -> t) -> (s -> t)
 W a b = a b b
 
 KI : {s t : Set} -> t -> s -> s
 KI = K I

 CI : {s t : Set} -> s -> (s -> t) -> t
 CI = C I

 CII : {s t : Set} -> ((s -> s)  -> t) -> t
 CII x = x I

 P : {s : Set} -> {t : Set} -> {u : Set} -> s -> t -> (s -> t -> u) -> u
 P x y f = f x y

{-
 b'2 : {u : Set} -> Ord -> _ -> Ord 
 b'2 Zero a = a K KI (a K)
 b'2 (Suc x) a = substn (a KI) (b'2 x (a K KI)) (a KI)
 b'2 (Lim phi) a = Lim (\n -> b'2 (phi n) (a K KI) (a K))
-}


 cantor : Ord -> Ord -> Ord
 cantor Zero a = Suc a
 cantor (Suc b) a = H _ (cantor b) a
 cantor (Lim f) a = Lim (\n -> cantor (f n) a)

 nabla : ford (1+ (1+ O))
 nabla f Zero = f Zero
 nabla f (Suc a) = f (Suc (nabla f a))
 nabla f (Lim h) = Lim (\n -> nabla f (h n))

 deriv : ford (1+ (1+ O))
 deriv f = nabla (H _ f)

 veblen : Ord -> Ord -> Ord
 veblen Zero = nabla (lim1 (\n -> rpt n (\x -> cantor x Zero)))
 veblen (Suc a) = nabla (lim1 (\n -> rpt n (veblen a)))
 veblen (Lim f) = nabla (lim1 (\n -> veblen (f n)))

 veb : Ord -> Ord
 veb a = veblen a Zero

 epsilon0 : Ord
 epsilon0 = veb Zero

 Gamma0 : Ord
 Gamma0 = Lim (\n -> rpt n veb Zero)

 epsilon : Ord -> Ord
 epsilon a = veblen Zero a

 veblen2 : Ord -> Ord -> Ord
 veblen2 Zero a = epsilon a
 veblen2 (Suc b) Zero = Lim (\n -> rpt n (veblen2 b) Zero)
 veblen2 (Suc b) (Suc a) = Lim (\n -> rpt n (veblen2 b) (Suc (veblen2 (Suc b) a)))
 veblen2 (Suc b) (Lim f) = Lim (\n -> veblen2 (Suc b) (f n))
 veblen2 (Lim f) Zero = Lim (\n -> veblen2 (f n) Zero)
 veblen2 (Lim f) (Suc a) = Lim (\n -> veblen2 (f n) (Suc (veblen2 (Lim f) a)))
 veblen2 (Lim f) (Lim g) = Lim (\n -> veblen2 (Lim f) (g n))

{-
 veblen3 : Ord -> Ord -> Ord -> Ord
 veblen3 Zero b a = veblen b a
 veblen3 (Suc c) Zero a = Lim (\n -> rpt n (\x -> veblen3 c x a) Zero)
 veblen3 (Suc c) (Suc b) Zero = Lim (\n -> rpt n (veblen3 (Suc c) b) Zero)
 veblen3 (Suc c) (Suc b) (Suc a) = Lim (\n -> rpt n (veblen3 (Suc c) b) (Suc (veblen3 (Suc c) (Suc b) a)))
 veblen3 (Suc c) (Suc b) (Lim f) = Lim (\n -> veblen3 (Suc c) (Suc b) (f n))
 veblen3 (Suc c) (Lim f) Zero = Lim (\n -> veblen3 (Suc c) (f n) Zero)
 veblen3 (Suc c) (Lim f) (Suc a) = Lim (\n -> veblen3 (Suc c) (f n) (Suc (veblen3 (Suc c) (Lim f) a)))
 veblen3 (Suc c) (Lim f) (Lim g) = Lim (\n -> veblen3 (Suc c) (Lim f) (g n))
 veblen3 (Lim f) b a = Lim (\n -> veblen3 (f n) b a)
-}
{-
 veblen4 : Ord -> Ord -> Ord -> Ord -> Ord
 veblen4 Zero c b a = veblen3 c b a
 veblen4 (Suc d) Zero b a = Lim (\n -> rpt n (\x -> veblen4 d x b a) Zero)
 veblen4 (Suc d) (Suc c) b Zero = Lim (\n -> rpt n (veblen4 (Suc d) c b) Zero)
 veblen4 (Suc d) (Suc c) b (Suc a) = Lim (\n -> rpt n (veblen4 (Suc d) c b) (Suc (veblen4 (Suc d) (Suc c) b a)))
 veblen4 (Suc d) (Suc c) b (Lim f) = Lim (\n -> rpt n (veblen4 (Suc d) (Suc c) b) (f n))
 veblen4 (Suc d) (Lim f) b Zero = Lim (\n -> veblen4 (Suc d) (f n) b Zero)
 veblen4 (Suc d) (Lim f) b (Suc a) = Lim (\n -> veblen4 (Suc d) (f n) b (Suc (veblen4 (Suc d) (Lim f) b a)))
 veblen4 (Suc d) (Lim f) b (Lim g) = Lim (\n -> veblen4 (Suc d) (Lim f) b (g n))
 veblen4 (Lim f) c b a = Lim (\n -> veblen4 (f n) c b a)
-}
{- 
 phi(an,...,a0) is defined by :
 phi(a) = w^a
 phi(0,an,...,a0) = phi(an,...,a0)
 phi(an,...,a(i+1),a,0,...,0,c) = c-th fixed point of \x.phi(an,...,a(i+1),b,x,0,...,0) for all b<a

 first fixed point of f = Lim (\n -> rpt n f Zero)
 n+1th fixed point of f = Lim (\n -> rpt n f (nth fixed point of f)

 phi(bn, bn-1, ..., br, 0, ..., 0, a) = a-th fixed point of x -> phi(cn, cn-1, ..., cr, x, 0, 0, ..., 0) for (cn, ..., cr) lexicographically less than (bn, ..., br) (the leftmost variable having the most weight) with the convention that phi(0, bn-1, ..., b0) = phi(bn-1, ..., b0).
-}
{-
 veblen3 : Ord -> Ord -> Ord -> Ord
 veblen3 Zero b a = veblen b a
 -- veblen3 (Suc c) Zero a = a-th fixed point of \x -> veblen3 c x Zero
 veblen3 (Suc c) Zero Zero = Lim (\n -> rpt n (\x -> veblen3 c x Zero) Zero)
 veblen3 (Suc c) Zero (Suc a) = Lim (\n -> rpt n (\x -> veblen3 c x Zero) (veblen3 (Suc c) Zero a))
 veblen3 (Suc c) Zero (Lim f) = Lim (\n -> veblen3 (Suc c) Zero (f n))
 veblen3 (Suc c) (Suc b) a = veblen3 c (Suc (veblen3 (Suc c) b a)) a
 veblen3 (Suc c) (Lim f) a = Lim (\n -> veblen3 (Suc c) (f n) a)
 veblen3 (Lim f) b a = Lim (\n -> veblen3 (f n) b a)
-}

 veblen3 : Ord -> Ord -> Ord -> Ord
 veblen3 Zero b a = veblen b a
 -- veblen3 (Suc c) Zero a = a-th fixed point of \x -> veblen3 c x Zero
 veblen3 (Suc c) Zero Zero = Lim (\n -> rpt n (\x -> veblen3 c x Zero) Zero)
 veblen3 (Suc c) Zero (Suc a) = Lim (\n -> rpt n (\x -> veblen3 c x Zero) (Suc (veblen3 (Suc c) Zero a)))
 veblen3 (Suc c) Zero (Lim f) = Lim (\n -> veblen3 (Suc c) Zero (f n))
 veblen3 (Suc c) (Suc b) Zero = Lim (\n -> rpt n (\x -> veblen3 (Suc c) b x) Zero)
 veblen3 (Suc c) (Suc b) (Suc a) = Lim (\n -> rpt n (\x -> veblen3 (Suc c) b x) (Suc (veblen3 (Suc c) (Suc b) a)))
 veblen3 (Suc c) (Suc b) (Lim f) = Lim (\n -> veblen3 (Suc c) (Suc b) (f n))
 veblen3 (Suc c) (Lim f) a = Lim (\n -> veblen3 (Suc c) (f n) a)
 veblen3 (Lim f) b a = Lim (\n -> veblen3 (f n) b a)

 phi1 : Ord -> Ord
 phi1 a = cantor a Zero

 phi2 : Ord -> Ord -> Ord
 phi2 Zero a = phi1 a
 phi2 (Suc b) Zero = H0 (phi2 b) Zero
 phi2 (Suc b) (Suc a) = H0 (phi2 b) (Suc (phi2 (Suc b) a))
 phi2 (Suc b) (Lim f) = Lim (\n -> phi2 (Suc b) (f n))
 phi2 (Lim f) a = Lim (\n -> phi2 (f n) a)

 phi3 : Ord -> Ord -> Ord -> Ord
 phi3 Zero b a = phi2 b a
 phi3 (Suc c) Zero Zero = H0 (\x -> phi3 c x Zero) Zero
 phi3 (Suc c) Zero (Suc a) = H0 (\x -> phi3 c x Zero) (Suc (phi3 (Suc c) Zero a))
 phi3 (Suc c) Zero (Lim f) = Lim (\n -> phi3 (Suc c) Zero (f n))
 phi3 (Suc c) (Suc b) Zero = H0 (phi3 (Suc c) b) Zero
 phi3 (Suc c) (Suc b) (Suc a) = H0 (phi3 (Suc c) b) (Suc (phi3 (Suc c) (Suc b) a))
 phi3 (Suc c) (Suc b) (Lim f) = Lim (\n -> phi3 (Suc c) (Suc b) (f n))
 phi3 (Suc c) (Lim f) a = Lim (\n -> phi3 (Suc c) (f n) a)
 phi3 (Lim f) b a = Lim (\n -> phi3 (f n) b a)

{-
 phi4 : Ord -> Ord -> Ord -> Ord -> Ord
 phi4 Zero c b a = phi3 c b a
 phi4 (Suc d) Zero Zero Zero = H0 (\x -> phi4 d x Zero Zero) Zero
 phi4 (Suc d) Zero Zero (Suc a) = H0 (\x -> phi4 d x Zero Zero) (Suc (phi4 (Suc d) Zero Zero a))
 phi4 (Suc d) Zero Zero (Lim f) = Lim (\n -> phi4 (Suc d) Zero Zero (f n))
 phi4 (Suc d) Zero (Suc b) Zero = H0 (phi4 (Suc d) Zero b) Zero
 phi4 (Suc d) Zero (Suc b) (Suc a) = H0 (phi4 (Suc d) Zero b) (Suc (phi4 (Suc d) Zero (Suc b) a))
 phi4 (Suc d) Zero (Suc b) (Lim f) = Lim (\n -> phi4 (Suc d) Zero (Suc b) (f n))
 phi4 (Suc d) Zero (Lim f) a = Lim (\n -> phi4 (Suc d) Zero (f n) a)
 phi4 (Suc d) (Suc c) Zero Zero = H0 (\x -> phi4 (Suc d) c x Zero) Zero
 phi4 (Suc d) (Suc c) Zero (Suc a) = H0 (\x -> phi4 (Suc d) c x Zero) (Suc (phi4 (Suc d) (Suc c) Zero a))
 phi4 (Suc d) (Suc c) Zero (Lim f) = Lim (\n -> phi4 (Suc d) (Suc c) Zero (f n))
 phi4 (Suc d) (Suc c) (Suc b) Zero = H0 (phi4 (Suc d) (Suc c) b) Zero
 phi4 (Suc d) (Suc c) (Suc b) (Suc a) = H0 (phi4 (Suc d) (Suc c) b) (Suc (phi4 (Suc d) (Suc c) (Suc b) a))
 phi4 (Suc d) (Suc c) (Suc b) (Lim f) = Lim (\n -> phi4 (Suc d) (Suc c) (Suc b) (f n))
 phi4 (Suc d) (Suc c) (Lim f) a = Lim (\n -> phi4 (Suc d) (Suc c) (f n) a)
 phi4 (Suc d) (Lim f) b a = Lim (\n -> phi4 (Suc d) (f n) b a)
 phi4 (Lim f) c b a = Lim (\n -> phi4 (f n) c b a)
-}

 phi4 : Ord -> Ord -> Ord -> Ord -> Ord
 phi4 Zero c b a = phi3 c b a
 phi4 d c (Suc b) Zero = H0 (\x -> phi4 d c b x) Zero
 phi4 d c (Suc b) (Suc a) = H0 (\x -> phi4 d c b x) (Suc (phi4 d c (Suc b) a))
 -- phi4 d c (Suc b) (Lim f) = Lim (\n -> phi4 d c (Suc b) (f n))
 phi4 d (Suc c) Zero Zero = H0(\x -> phi4 d c x Zero) Zero
 phi4 d (Suc c) Zero (Suc a) = H0 (\x -> phi4 d c x Zero) (Suc (phi4 d (Suc c) Zero a))
 phi4 (Suc d) Zero Zero Zero = H0 (\x -> phi4 d x Zero Zero) Zero
 phi4 (Suc d) Zero Zero (Suc a) = H0 (\x -> phi4 d x Zero Zero) (Suc (phi4 (Suc d) Zero Zero a))
 phi4 d c b (Lim f) = Lim (\n -> phi4 d c b (f n))
 phi4 d c (Lim f) a = Lim (\n -> phi4 d c (f n) a)
 phi4 d (Lim f) b a = Lim (\n -> phi4 d (f n) b a)
 phi4 (Lim f) c b a = Lim (\n -> phi4 (f n) c b a)

