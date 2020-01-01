module Madore where

 ident x = x

 comp f g x = f (g x)

 data Ord 
  = Zero
  | Suc Ord
  | Lim Ord (Ord -> Ord)

 one = Suc Zero
 two = Suc one

 instance Show Ord where
  show Zero = "Zero"
  show (Suc a) = "(Suc " ++ show a ++ ")"
  show (Lim n f) = "(Lim " ++ show n ++ " " ++ 
   show (f Zero) ++ "," ++ show (f one) ++ "," ++ show (f two) ++",..." ++ ")"

 omega = Lim Zero ident
 omega_plus_one = Suc omega

 omega1 = Lim one ident
 omega2 = Lim two ident

 -- plus a b = b+a
 plus Zero b = b
 plus (Suc a) b = Suc (plus a b)
 plus (Lim n f) b = Lim n (\x -> plus (f x) b)

 -- times a b = b.a
 times Zero b = Zero
 times (Suc a) b = plus b (times a b)
 times (Lim n f) b = Lim n (\x -> times (f x) b)

 -- power a b = b^a
 power Zero b = one
 power (Suc a) b = times b (power a b)
 power (Lim n f) b = Lim n (\x -> power (f x) b)

 -- power of a funcion : fpower0 a f = f^a
 fpower Zero f = ident
 fpower (Suc a) f = comp f (fpower a f)
 fpower (Lim n g) f = \x -> Lim n (\y -> fpower (g y) f x)
 
 epsilon0 = fpower omega (\x -> power x omega) Zero

 -- Madore psi
 madore Zero = epsilon0
 madore (Suc a) = fpower omega (\x -> power x (madore a)) Zero
 madore (Lim Zero g) = Lim Zero (comp madore g)
 madore (Lim (Suc Zero) g) = Lim Zero (\n -> fpower n (comp madore g) (madore Zero))
 
