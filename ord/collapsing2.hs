module Collapsing where

 -- Natural numbers
 data Nat 
  = ZeroN
  | SucN Nat

 -- Countable ordinals
 data Cord 
  = Zero
  | Suc Cord
  | Lim (Nat -> Cord)

 -- Ordinals
 data Ord
  = Cnt Cord
  | Ext (Cord -> Ord)

 -- Ordinal corresponding to a given natural
 ordOfNat ZeroN = Zero
 ordOfNat (SucN n) = Suc (ordOfNat n)

 -- omega
 w = Lim ordOfNat

 -- plus a b = b + a
 plus Zero b = b
 plus (Suc a) b = Suc (plus a b)
 plus (Lim s) b = Lim (\n -> plus (s n) b)

 iter f ZeroN a = a
 iter f (SucN p) a = iter f p (f a)

 opLim f a = Lim (\n -> f n a)

 opItw f = opLim (iter f)

 lim0 s = Lim s

 fpower l f Zero x = x
 fpower l f (Suc a) x = f (fpower l f a x)
 fpower l f (Lim s) x = l (\n -> fpower l f (s n) x)

 -- fix f z = least fixed point of f which is > z
 fix f z = fpower lim0 f w (Suc z) -- Lim (\n -> fpower0 f (ordOfNat n) (Suc z))

 -- cantor b a = a + w^b
 cantor Zero a = Suc a
 cantor (Suc b) a = fix (cantor b) a
 cantor (Lim s) a = Lim (\n -> cantor (s n) a)
 
  -- expw a = w^a
 expw a = cantor a Zero

 nabla f Zero = f Zero
 nabla f (Suc a) = f (Suc (nabla f a))
 nabla f (Lim s) = Lim (\n -> nabla f (s n))

 deriv f = nabla (opItw f)

 veblen Zero = nabla (opLim (iter (\a -> cantor a Zero)))
 veblen (Suc a) = nabla (opLim (iter (veblen a)))
 veblen (Lim s) = nabla (opLim (\n -> veblen (s n)))

 epsilon = veblen Zero 

 o = Ext (\a -> Cnt a)
 o2 = Ext (\a -> Ext (\b -> Cnt (plus a b)))

 psi (Cnt a) = epsilon a

