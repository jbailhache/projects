module Binveb where
 
 data Nat 
  = ZeroN 
  | SucN Nat

 data Ord 
  = Zero 
  | Suc Ord 
  | Lim (Nat -> Ord)

 iter f ZeroN x = x
 iter f (SucN n) x = f (iter f n x)

 opLim f a = Lim (\n -> f n a)

 opItw f = opLim (iter f)

 cantor a Zero = Suc a
 cantor a (Suc b) = opItw (\x -> cantor x b) a
 cantor a (Lim f) = Lim (\n -> cantor a (f n))

 nabla f Zero = f Zero
 nabla f (Suc a) = f (Suc (nabla f a))
 nabla f (Lim h) = Lim (\n -> nabla f (h n))

 deriv f = nabla (opItw f)

 binveb Zero = nabla (opLim (iter (cantor Zero)))
 binveb (Suc a) = nabla (opLim (iter (binveb a)))
 binveb (Lim f) = nabla (opLim (\n -> binveb (f n)))

