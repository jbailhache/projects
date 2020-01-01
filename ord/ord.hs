module Ord where

 ident x = x

 data Ord
  = Zero
  | Suc Ord
  | Lim Ord (Ord -> Ord)

 -- plus a b = b + a
 plus Zero b = b
 plus (Suc a) b = Suc (plus a b)
 plus (Lim n s) b = Lim n (\x -> plus (s x) b)

 -- times a b = b * a
 times Zero b = Zero
 times (Suc a) b = plus b (times a b)
 times (Lim n s) b = Lim n (\x -> times (s x) b)

 -- power a b = b^a
 power Zero b = Suc Zero
 power (Suc a) b = times b (power a b)
 power (Lim n s) b = Lim n (\x -> power (s x) b)

 one = Suc Zero
 omega = Lim Zero ident
 omegaplus1 = Suc omega
 omegatimes2 = plus omega omega
 omegapower2 = times omega omega
 omegapoweromega = power omega omega

 omega1 = Lim (Suc Zero) ident





