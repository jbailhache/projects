module ordi where

 data nat : Set where 
  O : nat
  S : nat -> nat

 data ordinal : Set where
  Zero : ordinal
  Succ : ordinal -> ordinal
  Limit : (nat -> ordinal) -> ordinal

 iter : (a : Set) (f : a -> a) (n : nat) (x : a) -> a
 iter a f O x = x
 iter a f (S p) x = iter a f p (f x)

 OpLim : (nat -> ordinal -> ordinal) -> ordinal -> ordinal
 OpLim F a = Limit (\n -> F n a) 

 OpItw : (ordinal -> ordinal) -> ordinal -> ordinal
 OpItw f = OpLim (iter _ f)

 cantor : ordinal -> ordinal -> ordinal 
 cantor a Zero = Succ a
 cantor a (Succ b) = OpItw (\x -> cantor x b) a 
 cantor a (Limit f) = Limit (\n -> cantor a (f n)) 

 Nabla : (ordinal -> ordinal) -> ordinal -> ordinal
 Nabla f Zero = f Zero
 Nabla f (Succ a) = f (Succ (Nabla f a)) 
 Nabla f (Limit h) = Limit (\n -> Nabla f (h n)) 

 deriv : (ordinal -> ordinal) -> ordinal -> ordinal 
 deriv f = Nabla (OpItw f) 

 veblen : ordinal -> ordinal -> ordinal 
 veblen Zero = Nabla (OpLim (iter _ (cantor Zero)))
 veblen (Succ a) = Nabla (OpLim (iter _ (veblen a))) 
 veblen (Limit f) = Nabla (OpLim (\n -> veblen (f n))) 

 veb : ordinal -> ordinal
 veb a = veblen a Zero

 epsilon0 : ordinal
 epsilon0 = veb Zero

 Gamma0 : ordinal
 Gamma0 = Limit (\n -> iter _ veb n Zero) 

