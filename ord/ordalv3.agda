{- 
   A definition of the large Veblen ordinal and after in Agda
   by Jacques Bailhache, March 2016

   See https://en.wikipedia.org/wiki/Veblen_function

    (1) φ(α)=ω**α for a single variable,

    (2) φ(0,αn−1,…,α0)=φ(αn−1,…,α0), and

    (3) for α>0, γ↦φ(αn,…,αi+1,α,0,…,0,γ) is the function enumerating the common fixed points of the functions ξ↦φ(αn,…,αi+1,β,ξ,0,…,0) for all β<α.

    (4) Let α be a transfinite sequence of ordinals (i.e., an ordinal function with finite support) which ends in zero (i.e., such that α₀=0), and let α[0↦γ] denote the same function where the final 0 has been replaced by γ. Then γ↦φ(α[0↦γ]) is defined as the function enumerating the common fixed points of all functions ξ↦φ(β) where β ranges over all sequences which are obtained by decreasing the smallest-indexed nonzero value of α and replacing some smaller-indexed value with the indeterminate ξ (i.e., β=α[ι₀↦ζ,ι↦ξ] meaning that for the smallest index ι₀ such that αι₀ is nonzero the latter has been replaced by some value ζ<αι₀ and that for some smaller index ι<ι₀, the value αι=0 has been replaced with ξ).

-}

module ordalv where

 data Nat : Set where
  O : Nat
  1+ : Nat -> Nat

 data Ord : Set where
  Zero : Ord
  Suc : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord

 -- rpt n f x = f^n(x)
 rpt : {t : Set} -> Nat -> (t -> t) -> t -> t
 rpt O f x = x
 rpt (1+ n) f x = rpt n f (f x)

 -- smallest fixed point of f greater than x, limit of x, f x, f (f x), ...
 fix : (Ord -> Ord) -> Ord -> Ord
 fix f x = Lim (\n -> rpt n f x)

 w = fix Suc Zero -- not a fixed point in this case !

 -- cantor b a = a + w^b
 cantor : Ord -> Ord -> Ord
 cantor Zero a = Suc a
 cantor (Suc b) a = fix (cantor b) a
 cantor (Lim f) a = Lim (\n -> cantor (f n) a)

 -- increase a = w^a
 increase : Ord -> Ord
 increase a = cantor a Zero

 -- Another possible increase function
 -- this gives a phi function which grows slower
{-
 increase : Ord -> Ord
 increase Zero = Suc Zero
 increase (Suc a) = Suc (increase a)
 increase (Lim f) = Lim (\n -> increase (f n))
-}

 -- Associative list of ordinals
 infixr 40 _=>_&_
 data OrdAList : Set where
  Zeros : OrdAList
  _=>_&_ : Ord -> Ord -> OrdAList -> OrdAList

 -- Usage : phi al, where al is the associative list of couples index => value ordered by increasing values,
 -- absent indexes corresponding to Zero values
 phi : OrdAList -> Ord
 phi              Zeros  = increase Zero -- (1) phi(0) = w**0 = 1
 phi (Zero => a & Zeros) = increase a    -- (1) phi(a) = w**a
 phi (            k => Zero & al) = phi al -- eliminate unnecessary Zero value
 phi (Zero => a & k => Zero & al) = phi (Zero => a & al) -- idem
 phi (Zero => a & Zero => b & al) = phi (Zero => a & al) -- should not appear but necessary for completeness
 phi (Zero => Lim f & al) = Lim (\n -> phi (Zero => f n & al)) -- canonical treatment of limit
 phi (            k => Lim f & al) = Lim (\n -> phi (k => f n & al)) -- idem
 phi (Zero => a & k => Lim f & al) = Lim (\n -> phi (Zero => a & k => f n & al)) -- idem 
 phi (                Suc k => Suc b & al) = fix (\x -> phi (k => x & Suc k => b & al)) Zero -- (3) least fixed point
 phi (Zero => Suc a & Suc k => Suc b & al) = fix (\x -> phi (k => x & Suc k => b & al)) (Suc (phi (Zero => a & Suc k => Suc b & al))) -- (3) following fixed points
 phi (                Lim f => Suc b & al) = Lim (\n -> fix (\x -> phi (f n => x & Lim f => b & al)) Zero) -- (4) least fixed point
 phi (Zero => Suc a & Lim f => Suc b & al) = Lim (\n -> fix (\x -> phi (f n => x & Lim f => b & al)) (Suc (phi (Zero => a & Lim f => Suc b & al)))) -- (4) following fixed points 

 SmallVeblen = phi (w => Suc Zero & Zeros)

 LargeVeblen = fix (\x -> phi (x => Suc Zero & Zeros)) Zero

 alv0 : Ord -> Ord
 alv0 Zero    = fix (\x -> phi (x => Suc Zero & Zeros)) Zero -- Large Veblen
 alv0 (Suc a) = fix (\x -> phi (x => Suc Zero & Zeros)) (Suc (alv0 a))
 alv0 (Lim f) = Lim (\n -> alv0 (f n))

 alv1 : Ord -> Ord
 alv1 Zero    = fix (\x -> alv0 x) Zero
 alv1 (Suc a) = fix (\x -> alv0 x) (Suc (alv1 a))
 alv1 (Lim f) = Lim (\n -> alv1 (f n))

 -- alv1 x = phi1 (Zero => x & Suc Zero => Suc Zero & Zeros)

 phi1 : OrdAList -> Ord
 phi1              Zeros  = alv0 Zero -- (1) phi(0) = w**0 = 1
 phi1 (Zero => a & Zeros) = alv0 a    -- (1) phi(a) = w**a
 phi1 (            k => Zero & al) = phi1 al -- eliminate unnecessary Zero value
 phi1 (Zero => a & k => Zero & al) = phi1 (Zero => a & al) -- idem
 phi1 (Zero => a & Zero => b & al) = phi1 (Zero => a & al) -- should not appear but necessary for completeness
 phi1 (Zero => Lim f & al) = Lim (\n -> phi1 (Zero => f n & al)) -- canonical treatment of limit
 phi1 (            k => Lim f & al) = Lim (\n -> phi1 (k => f n & al)) -- idem
 phi1 (Zero => a & k => Lim f & al) = Lim (\n -> phi1 (Zero => a & k => f n & al)) -- idem 
 phi1 (                Suc k => Suc b & al) = fix (\x -> phi1 (k => x & Suc k => b & al)) Zero -- (3) least fixed point
 phi1 (Zero => Suc a & Suc k => Suc b & al) = fix (\x -> phi1 (k => x & Suc k => b & al)) (Suc (phi1 (Zero => a & Suc k => Suc b & al))) -- (3) following fixed points
 phi1 (                Lim f => Suc b & al) = Lim (\n -> fix (\x -> phi1 (f n => x & Lim f => b & al)) Zero) -- (4) least fixed point
 phi1 (Zero => Suc a & Lim f => Suc b & al) = Lim (\n -> fix (\x -> phi1 (f n => x & Lim f => b & al)) (Suc (phi1 (Zero => a & Lim f => Suc b & al)))) -- (4) following fixed points 

 phiinc : (Ord -> Ord) -> OrdAList -> Ord
 phiinc inc              Zeros  = inc Zero -- (1) phi(0) = w**0 = 1
 phiinc inc (Zero => a & Zeros) = inc a    -- (1) phi(a) = w**a
 phiinc inc (            k => Zero & al) = phiinc inc al -- eliminate unnecessary Zero value
 phiinc inc (Zero => a & k => Zero & al) = phiinc inc (Zero => a & al) -- idem
 phiinc inc (Zero => a & Zero => b & al) = phiinc inc (Zero => a & al) -- should not appear but necessary for completeness
 phiinc inc (Zero => Lim f & al) = Lim (\n -> phiinc inc (Zero => f n & al)) -- canonical treatment of limit
 phiinc inc (            k => Lim f & al) = Lim (\n -> phiinc inc (k => f n & al)) -- idem
 phiinc inc (Zero => a & k => Lim f & al) = Lim (\n -> phiinc inc (Zero => a & k => f n & al)) -- idem 
 phiinc inc (                Suc k => Suc b & al) = fix (\x -> phiinc inc (k => x & Suc k => b & al)) Zero -- (3) least fixed point
 phiinc inc (Zero => Suc a & Suc k => Suc b & al) = fix (\x -> phiinc inc (k => x & Suc k => b & al)) (Suc (phiinc inc (Zero => a & Suc k => Suc b & al))) -- (3) following fixed points
 phiinc inc (                Lim f => Suc b & al) = Lim (\n -> fix (\x -> phiinc inc (f n => x & Lim f => b & al)) Zero) -- (4) least fixed point
 phiinc inc (Zero => Suc a & Lim f => Suc b & al) = Lim (\n -> fix (\x -> phiinc inc (f n => x & Lim f => b & al)) (Suc (phiinc inc (Zero => a & Lim f => Suc b & al)))) -- (4) following fixed points 

 phi' = phiinc increase
 phi1' = phiinc alv0

{-
 alvph : (OrdAList -> Ord) -> Ord -> Ord
 alvph ph Zero    = fix (\x -> ph (x => Suc Zero & Zeros)) Zero 
 alvph ph (Suc a) = fix (\x -> ph (x => Suc Zero & Zeros)) (Suc (alvph ph a))
 alvph ph (Lim f) = Lim (\n -> alvph ph (f n))
-}

 incphi : (OrdAList -> Ord) -> Ord -> Ord
 incphi ph Zero    = fix (\x -> ph (x => Suc Zero & Zeros)) Zero 
 incphi ph (Suc a) = fix (\x -> ph (x => Suc Zero & Zeros)) (Suc (incphi ph a))
 incphi ph (Lim f) = Lim (\n -> incphi ph (f n))

 phi'' = phiinc increase
 phi1'' = phiinc (incphi phi'')

 phiord : Ord -> OrdAList -> Ord
 phiord Zero = phiinc increase
 phiord (Suc a) = phiinc (incphi (phiord a))
 phiord (Lim f) = \ph -> Lim (\n -> phiord (f n) ph)

 inc0 = increase
 inc1 = incphi (phiinc inc0)
 
 incord : Ord -> Ord -> Ord
 incord Zero = increase
 incord (Suc a) = incphi (phiinc (incord a))
 incord (Lim f) = \x -> Lim (\n -> incord (f n) x)

 MyLargeOrdinal = fix (\x -> incord x x) (Suc Zero)


{-
Normally it should terminate because the parameter of phi lexicographically decreases, but Agda is not clever enough to see it, 
so it must be called with no termination check option :

$ agda -I --no-termination-check LargeVeblen.agda
                 _ 
   ____         | |
  / __ \        | |
 | |__| |___  __| | ___
 |  __  / _ \/ _  |/ __\     Agda Interactive
 | |  |/ /_\ \/_| / /_| \
 |_|  |\___  /____\_____/    Type :? for help.
        __/ /
        \__/

The interactive mode is no longer supported. Don't complain if it doesn't work.
Checking LargeVeblen (/perso/ord/LargeVeblen.agda).
Finished LargeVeblen.
Main> phi Zeros
Suc Zero
Main> phi (Zero => Suc Zero & Zeros)
Lim (λ n → rpt n (λ a → Suc a) Zero)
Main> phi (Zero => Suc (Suc Zero) & Zeros)
Lim
(λ n → rpt n (λ a → Lim (λ n₁ → rpt n₁ (λ a₁ → Suc a₁) a)) Zero)
Main> phi (Suc Zero => Suc Zero & Zeros)
Lim
(λ n →
   rpt n (λ x → phi (Zero => x & Suc Zero => Zero & Zeros)) Zero)
Main> 
-}

