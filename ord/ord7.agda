module ord where

 data Nat : Set where
  zn : Nat
  sn : Nat -> Nat

 data Ord : Set where
  zo : Ord
  so : Ord -> Ord
  lo : (Nat -> Ord) -> Ord

 ordofnat : Nat -> Ord
 ordofnat zn = zo
 ordofnat (sn n) = so (ordofnat n)

 w : Ord
 w = lo ordofnat

 repeat : (a : Set) -> (n : Nat) -> (f : a -> a) -> (x : a) -> a
 repeat _ zn f x = x
 repeat a (sn p) f x = repeat a p f (f x)

 plusw : Ord -> Ord
 plusw x = lo (\(n : Nat) -> repeat _ n so x)

 w1 = plusw zo

 wx2 = plusw (plusw zo)

 wp2 = lo (\(n : Nat) -> repeat _ n plusw zo)

 pluswp2 : Ord -> Ord
 pluswp2 x = lo (\(n : Nat) -> repeat _ n plusw x)

 H0 : (f : Ord -> Ord) -> (x : Ord) -> Ord
 H0 f x = lo (\(n : Nat) -> repeat _ n f x)

 w2 = H0 so zo

 H1 : (f : (Ord -> Ord) -> (Ord -> Ord)) -> (g : Ord -> Ord) -> (x : Ord) -> Ord 
 H1 f g x = lo (\(n : Nat) -> repeat _ n f g x)

 wpw = H1 H0 so zo

 ford : Nat -> Set
 ford zn = Ord
 ford (sn n) = ford n -> ford n

 lim1 : (Nat -> Ord -> Ord) -> Ord -> Ord
 lim1 f x = lo (\(p : Nat) -> f p x)

 limn : (n : Nat) -> (Nat -> ford n) -> ford n
 limn zn f = lo f
 limn (sn p) f = \x -> limn p (\q -> f q x)

 I : {s : Set} -> s -> s
 I a = a

 K : {s t : Set} -> s -> t -> s
 K a b = a

 S : {s t u : Set} -> (s -> t -> u) -> (s -> t) -> s -> u
 S a b c = a c (b c)

 C : {s t u : Set} -> (s -> t -> u) -> t -> s -> u
 C a b c = a c b

 B : {s t u : Set} -> (s -> t) -> (u -> s) -> u -> t
 B a b c = a (b c)

 W : {s t u : Set} -> (s -> s -> t) -> s -> t
 W a b = a b b

 KI : {s t : Set} -> t -> s -> s
 KI = K I

 CI : {s t : Set} -> s -> (s -> t) -> t
 CI = C I

 CII : {s t : Set} -> ((s -> s) -> t) -> t
 CII x = x I

 insert : {s t u : Set} -> s -> (t -> u) -> (s -> t) -> u
 insert x a f = a (f x)

 -- nuplet zn  = CII
 -- nuplet (sn n) f x = nuplet n (\(s) -> insert x s)


  
