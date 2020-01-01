module Lvo where

 data Nat 
  = ZeroN 
  | SucN Nat

 data Ordi 
  = Zero 
  | Suc Ordi 
  | Lim (Nat -> Ordi)

 rpt ZeroN f x = x
 rpt (SucN n) f x = rpt n f (f x)

 fix f x = Lim (\n -> rpt n f x)

 w = fix Suc Zero

 cantor Zero a = Suc a
 cantor (Suc b) a = fix (cantor b) a
 cantor (Lim f) a = Lim (\n -> cantor (f n) a)

 increase a = cantor a Zero

 data OrdiAList 
  = Zeros
  | Ass Ordi Ordi OrdiAList

 phi Zeros = increase Zero
 phi (Ass Zero a Zeros) = increase a
 phi (Ass k Zero al) = phi al
 phi (Ass Zero a (Ass k Zero al)) = phi (Ass Zero a al)
 phi (Ass Zero a (Ass Zero b al)) = phi (Ass Zero a al)
 phi (Ass Zero (Lim f) al) = Lim $ \n -> phi $ Ass Zero (f n) al
 phi (Ass (Suc k) (Suc b) al) = fix (\x -> phi $ Ass k x $ Ass (Suc k) b al) Zero
 phi (Ass Zero (Suc a) (Ass (Suc k) (Suc b) al)) = fix (\x -> phi $ Ass k x $ Ass (Suc k) b al) (Suc $ phi $ Ass Zero a $ Ass (Suc k) (Suc b) al)
 phi (Ass (Suc k) (Lim f) al) = Lim $ \n -> phi $ Ass (Suc k) (f n) al
 phi (Ass Zero (Suc a) (Ass (Suc k) (Lim f) al)) = Lim $ \n -> phi $ Ass k (Suc $ phi $ Ass Zero a $ Ass (Suc k) (Lim f) al) $ Ass (Suc k) (f n) al
 -- phi (Ass (Lim f) (Suc b) al) = Lim $ \n -> fix (\x -> phi $ Ass (f n) x $ Ass (Lim f) b al) Zero
 phi (Ass (Lim f) (Suc b) al) = Lim $ \n -> phi $ Ass (f n) (Suc Zero) $ Ass (Lim f) b al
 -- phi (Ass Zero (Suc a) (Ass (Lim f) (Suc b) al)) = Lim $ \n -> fix (\x -> phi $ Ass (f n) x $ Ass (Lim f) b al) (Suc $ phi $ Ass Zero a $ Ass (Lim f) (Suc b) al)
 phi (Ass Zero (Suc a) (Ass (Lim f) (Suc b) al)) = Lim $ \n -> phi $ Ass (f n) (phi $ Ass Zero a $ Ass (Lim f) (Suc b) al) $ Ass (Lim f) b al
 phi (Ass (Lim f) (Lim g) al) = Lim $ \n -> phi $ Ass (Lim f) (g n) al
 phi (Ass Zero (Suc a) (Ass (Lim f) (Lim g) al)) = Lim $ \n -> phi $ Ass (f n) (phi $ Ass Zero a $ Ass (Lim f) (Lim g) al) $ Ass (Lim f) (g n) al

 smallVeblen = phi $ Ass w (Suc Zero) Zeros
 largeVeblen = fix (\x -> phi $ Ass x (Suc Zero) Zeros) (Suc Zero)


 main = do
  putStrLn "Hello"

 
