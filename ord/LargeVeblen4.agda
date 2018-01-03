{- 
   A definition of the large Veblen ordinal in Agda
   by Jacques Bailhache, March 2016

   See https://en.wikipedia.org/wiki/Veblen_function

    (1) φ(α)=ω**α for a single variable,

    (2) φ(0,αn−1,…,α0)=φ(αn−1,…,α0), and

    (3) for α>0, γ↦φ(αn,…,αi+1,α,0,…,0,γ) is the function enumerating the common fixed points of the functions ξ↦φ(αn,…,αi+1,β,ξ,0,…,0) for all β<α.

    (4) Let α be a transfinite sequence of ordinals (i.e., an ordinal function with finite support) which ends in zero (i.e., such that α₀=0), and let α[0↦γ] denote the same function where the final 0 has been replaced by γ. Then γ↦φ(α[0↦γ]) is defined as the function enumerating the common fixed points of all functions ξ↦φ(β) where β ranges over all sequences which are obtained by decreasing the smallest-indexed nonzero value of α and replacing some smaller-indexed value with the indeterminate ξ (i.e., β=α[ι₀↦ζ,ι↦ξ] meaning that for the smallest index ι₀ such that αι₀ is nonzero the latter has been replaced by some value ζ<αι₀ and that for some smaller index ι<ι₀, the value αι=0 has been replaced with ξ).

-}

module LargeVeblen where

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

 -- cantor a b = b + w^a
 cantor : Ord -> Ord -> Ord
 cantor Zero a = Suc a
 cantor (Suc b) a = fix (cantor b) a
 cantor (Lim f) a = Lim (\n -> cantor (f n) a)

 -- phi0 a = w^a
 phi0 : Ord -> Ord
 phi0 a = cantor a Zero

 -- Another possibility is to use phi'0 instead of phi0 in the definition of phi,
 -- this gives a phi function which grows slower
 phi'0 : Ord -> Ord
 phi'0 Zero = Suc Zero
 phi'0 (Suc a) = Suc (phi'0 a)
 phi'0 (Lim f) = Lim (\n -> phi'0 (f n))

 -- Associative list of ordinals
 infixr 40 _=>_&_
 data OrdAList : Set where
  Zeros : OrdAList
  _=>_&_ : Ord -> Ord -> OrdAList -> OrdAList

 -- Usage : phi al, where al is the associative list of couples index => value ordered by increasing values,
 -- absent indexes corresponding to Zero values
 phi : OrdAList -> Ord 
 phi              Zeros  = phi0 Zero -- (1) phi(0) = w**0 = 1 
 phi (Zero => a & Zeros) = phi0 a    -- (1) phi(a) = w**a
 phi (            k => Zero & al) = phi al -- eliminate unnecessary Zero value
 phi (Zero => a & k => Zero & al) = phi (Zero => a & al) -- idem
 phi (Zero => a & Zero => b & al) = phi (Zero => a & al) -- should not appear but necessary for completeness
 phi (Zero => Lim f & al) = Lim (\n -> phi (Zero => f n & al)) -- canonical treatment of limit
 phi (                Suc k => Suc b & al) = fix (\x -> phi (k => x & Suc k => b & al)) Zero -- (3) least fixed point
 phi (Zero => Suc a & Suc k => Suc b & al) = fix (\x -> phi (k => x & Suc k => b & al)) (Suc (phi (Zero => a & Suc k => Suc b & al))) -- (3) following fixed points
 phi (                Suc k => Lim f & al) = Lim (\n -> phi (Suc k => f n & al)) -- idem 
 phi (Zero => Suc a & Suc k => Lim f & al) = Lim (\n -> phi (k => Suc (phi (Zero => a & Suc k => Lim f & al)) & Suc k => f n & al)) -- idem 
 -- phi (                Lim f => Suc b & al) = Lim (\n -> fix (\x -> phi (f n => x & Lim f => b & al)) Zero) -- (4) least fixed point
 phi (                Lim f => Suc b & al) = Lim (\n -> phi (f n => (Suc Zero) & Lim f => b & al))
 -- phi (Zero => Suc a & Lim f => Suc b & al) = Lim (\n -> fix (\x -> phi (f n => x & Lim f => b & al)) (Suc (phi (Zero => a & Lim f => Suc b & al)))) -- (4) following fixed points 
 phi (Zero => Suc a & Lim f => Suc b & al) = Lim (\n -> phi (f n => phi (Zero => a & Lim f => Suc b & al) & Lim f => b & al))
 phi (                Lim f => Lim g & al) = Lim (\n -> phi (Lim f => g n & al))
 phi (Zero => Suc a & Lim f => Lim g & al) = Lim (\n -> phi (f n => phi (Zero => a & Lim f => Lim g & al) & Lim f => g n & al)) 

 SmallVeblen = phi (w => Suc Zero & Zeros)

 LargeVeblen = fix (\x -> phi (x => Suc Zero & Zeros)) (Suc Zero)

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

