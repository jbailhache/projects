module Collapsing where

 -- Natural numbers
 data Nat 
  = ZeroN
  | SucN Nat

 -- Ordinals
 data Ord 
  = Zero
  | Suc Ord
  | Lim (Nat -> Ord)
  | Ext (Ord -> Ord)

 -- Ordinals
 --data Xord
 -- = Cnt Ord
 -- | Ext (Ord -> Xord)

 -- Ordinal corresponding to a given natural
 ordOfNat ZeroN = Zero
 ordOfNat (SucN n) = Suc (ordOfNat n)

 -- omega
 w = Lim ordOfNat

 -- plus a b = b + a
 plus Zero b = b
 plus (Suc a) b = Suc (plus a b)
 plus (Lim s) b = Lim (\n -> plus (s n) b)
 plus (Ext f) b = Ext (\x -> plus (f x) b)

 lim0 s = Lim s

{-
 fpower l f Zero x = x
 fpower l f (Suc a) x = f (fpower l f a x)
 fpower l f (Lim s) x = l (\n -> fpower l f (s n) x)

 -- fix f z = least fixed point of f which is > z
 fix f z = fpower lim0 f w (Suc z) -- Lim (\n -> fpower0 f (ordOfNat n) (Suc z))
-}

 iter f ZeroN a = a
 iter f (SucN p) a = iter f p (f a)

 opLim f a = Lim (\n -> f n a)

 opItw f = opLim (iter f)

 -- cantor a b = a + w^b
 cantor a Zero = Suc a
 cantor a (Suc b) = opItw (\x -> cantor x b) a
 cantor a (Lim s) = Lim (\n -> cantor a (s n))
 cantor a (Ext f) = Ext (\x -> cantor a (f x))
 
  -- expw a = w^a
 expw = cantor Zero 

 nabla f Zero = f Zero
 nabla f (Suc a) = f (Suc (nabla f a))
 nabla f (Lim s) = Lim (\n -> nabla f (s n))
 nabla f (Ext g) = Ext (\x -> nabla f (g x))

 deriv f = nabla (opItw f)

 veblen Zero = nabla (opLim (iter (cantor Zero)))
 veblen (Suc a) = nabla (opLim (iter (veblen a)))
 veblen (Lim s) = nabla (opLim (\n -> veblen (s n)))
 veblen (Ext f) = \a -> Ext (\x -> veblen (f x) a)

 epsilon = veblen Zero 

 fix f z = opItw f (Suc z)

 next = fix expw

 o = Ext (\x -> x)
 -- o2 = Ext (\x -> Ext (\y -> plus x y))
 o2 = Ext (\x -> plus x o)

 -- apply (Cnt a) b = a
 -- apply (Ext f) b = f b

 -- psi (Cnt a) = Cnt (epsilon a)
 -- psi (Ext f) = psi (opItw (\a -> f (psi a)) (Cnt Zero))
 -- psi (Ext f) = opItw (\a -> psi (f a)) (psi (Cnt Zero))
 -- psi (Ext f) = Ext (\a -> opItw (\b -> apply (f b) a) Zero)
 
 psi Zero = epsilon Zero
 psi (Suc a) = next (psi a)
 psi (Lim s) = Lim (\n -> psi (s n))
 psi (Ext f) = psi (opItw (\a -> f (psi a)) Zero)

