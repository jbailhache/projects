module Ord where

 ident x = x

 comp f g x = f (g x)

 data Ord 
  = Zero
  | Suc Ord
  | Lim Ord (Ord -> Ord)

 one = Suc Zero
 two = Suc one

 omega = Lim Zero ident
 omega_plus_one = Suc omega

 omega1 = Lim one ident

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
 
 omega_times_2 = Lim Zero (\x -> plus x omega)

 -- power of a funcion : fpower0 a f = f^a
 fpower0 Zero f = ident
 fpower0 (Suc a) f = comp f (fpower0 a f)
 fpower0 (Lim n g) f = \x -> Lim n (\y -> fpower0 (g y) f x)

 h0 = fpower0 omega
 
 omega_rhsz = h0 Suc Zero
 
 -- cofinality
 cof Zero = Zero
 cof (Suc a) = one
 cof (Lim n f) = Lim n ident

 -- ge a b = b>=a
 -- ge Zero b = True
 -- ge (Suc a) Zero = False
 -- ge (Suc a) (Suc b) = ge a b
 -- ge (Suc a) (Lim n f) = ?
 ge a b = True 

 -- Buchholz psi
 buchholz Zero Zero = one
 buchholz (Suc n) Zero = Lim (Suc n) ident
 buchholz (Lim m h) Zero = Lim m (\x -> buchholz (h x) Zero)
 buchholz n (Suc b) = times omega (buchholz n b)
 buchholz n (Lim m h) = if ge m n 
                        then Lim m (comp (buchholz n) h) 
                        else Lim Zero (\x -> fpower0 x (comp (buchholz n) h) (buchholz n Zero))
 -- buchholz (plus k m) (Lim m h) = Lim m (comp (buchholz (plus k m)) h)
 -- buchholz n (Lim m h) = Zero

