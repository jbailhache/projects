module ordml where

 I : {s : Set} -> s -> s
 I a = a

 K : {s t : Set} -> s -> t -> s
 K a b = a

 S : {s t u : Set} -> (s -> t -> u) -> (s -> t) -> (s -> u)
 S a b c = a c (b c)

 C : {s t u : Set} -> (s -> t -> u) -> (t -> s -> u) 
 C a b c = a c b

 B : {s t u : Set} -> (s -> t) -> (u -> s) -> (u -> t)
 B a b c = a (b c)

 W : {s t u : Set} -> (s -> s -> t) -> (s -> t)
 W a b = a b b
 
 KI : {s t : Set} -> t -> s -> s
 KI = K I

 CI : {s t : Set} -> s -> (s -> t) -> t
 CI = C I

 data Nat : Set where
  O : Nat
  1+ : Nat -> Nat

 data Ord : Set where
  Zero : Ord
  Suc : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord

 suc : Ord -> Ord
 suc x = Suc x

 lim' : (Nat -> Ord) -> Ord
 lim' f = Lim f

 OrdNat : Nat -> Ord
 OrdNat O = Zero
 OrdNat (1+ n) = Suc (OrdNat n)

 lim : (Ord -> Ord) -> Ord
 lim f = Lim (\(n  : Nat) -> f (OrdNat n))

 One : Ord
 One = Suc Zero
 
 omega : Ord
 omega = Lim OrdNat

 repeat : (a : Set) -> (n : Nat) -> (f : a -> a) -> (x : a) -> a
 repeat _ O f x = x
 repeat a (1+ p) f x = repeat a p f (f x)

 -- representation of naturals
 rep1 : {t : Set} -> t -> (t -> t) -> Nat -> t
 rep1 z s O = z
 rep1 z s (1+ x) = s (rep1 z s x) 

 rep' : (t : Set) -> t -> (t -> t) -> Nat -> t
 rep' _ z s O = z
 rep' t z s (1+ x) = s (rep' t z s x) 

 rep : {t : Set} -> t -> (t -> t) -> Nat -> t
 rep = rep' _

 rep'' : (t : Set) -> t -> (t -> t) -> Nat -> t
 rep'' _ z s O = z
 rep'' t z s (1+ x) = rep'' t (s z) s x

 -- representation of ordinals
 Rep : Ord -> (Ord -> Ord) -> Ord -> Ord
 Rep z s Zero = z
 Rep z s (Suc x) = s (Rep z s x)
 Rep z s (Lim f) = Lim (\(x : Nat) -> Rep z s (f x))

{-
 Rep' : (t : Set) -> t -> (t -> t) -> Ord -> t
 Rep' _ z s Zero = z
 Rep' t z s (Suc x) = s (Rep' t z s x)
 Rep' t z s (Lim f) = Lim (\(x : Nat) -> Rep' t z s (f x))
-}

 + : Nat -> Nat -> Nat
 + O y = y
 + (1+ x) y = 1+ (+ x y)

 plus : Ord -> Ord -> Ord
 plus Zero y = y
 plus (Suc x) y = Suc (plus x y)
 plus (Lim f) y = Lim (\(x : Nat) -> plus (f x) y)

 times : Ord -> Ord -> Ord
 times Zero y = y
 times (Suc x) y = plus y (times x y)
 times (Lim f) y = Lim (\(x : Nat) -> times (f x) y)

 power : Ord -> Ord -> Ord
 power Zero y = One
 power (Suc x) y = times y (power x y)
 power (Lim f) y = Lim (\(x : Nat) -> power (f x) y)

 hpower : Ord -> Ord -> Ord
 hpower Zero y = One
 hpower (Suc x) y = power y (hpower x y)
 hpower (Lim f) y = Lim (\(x : Nat) -> hpower (f x) y)

 plus' : Ord -> Ord -> Ord
 plus' a b = Rep b suc a

 times' : Ord -> Ord -> Ord
 times' a b = Rep Zero (plus' b) a

 power' : Ord -> Ord -> Ord
 power' a b = Rep (Suc Zero) (times' b) a

 op : Ord -> Ord -> Ord -> Ord
 op Zero x y = plus x y
 op (Suc Zero) x y = times x y
 op (Suc n) Zero y = One
 op (Suc n) (Suc Zero) y = y
 op (Suc n) (Suc x) y = op n y (op (Suc n) x y)
 op (Suc n) (Lim f) y = Lim (\(x : Nat) -> op (Suc n) (f x) y)
 op (Lim f) x y = Lim (\(n : Nat) -> op (f n) x y)
 
 op' : Ord -> Ord -> Ord -> Ord
 op' Zero x y = plus x y
 op' (Suc n) Zero y = y 
 op' (Suc n) (Suc x) y = op' n y (op' (Suc n) x y)
 op' (Suc n) (Lim f) y = Lim (\(x : Nat) -> op' (Suc n) (f x) y)
 op' (Lim f) x y = Lim (\(n : Nat) -> op' (f n) x y)

 epsilon0 : Ord
 epsilon0 = Lim (rep Zero (\(x : Ord) -> power x omega))

 epsilon0' : Ord
 epsilon0' = hpower omega omega

 epsilon0'' : Ord
 epsilon0'' = op (Suc (Suc (Suc (Suc Zero)))) (Suc (Suc Zero)) omega

 H : (Ord -> Ord) -> Ord -> Ord
 H f x = Lim (rep x f)
 -- H f x = Lim (\(n : Nat) -> repeat _ n f x)

 H' : {s : Set} -> (s -> Ord) -> (s -> s) -> s -> Ord
 H' phi f x = Lim (\(y : Nat) -> phi (rep x f y))

{-
	limit 0 f = (f 0) U (f 1) U ...
	limit 1 f x = (f 0 x) U ...
		= limit 0 (\p. f p x)

In ML :

let rec limit = function
	Zero -> lim |
	Suc n -> function f -> function x ->
		limit n (function p -> f p x);;

let rec limit n f = match n with
	Zero -> Lim f |
	Suc n -> function x -> limit n (function p -> f p x);;

problem:
	limit 0 is of type (Ord -> Ord) -> Ord
	limit 1 is of type (Ord -> (a->Ord)) -> (a->Ord)
	limit 2 is of type (Ord -> (a->b->Ord)) -> (a->b->Ord) ...

let hyper n phi f x = limit n (function y -> phi (rep x f y));;

let omega_power_omega = hyper 1 I (hyper 0 I) suc Zero;;
-}

{-
 lim1 : {s : Set} -> (Ord -> s -> Ord) -> s -> Ord
 lim1 f x = Lim (\(p : Nat) -> f (OrdNat p) x)

 lim2 : {s t : Set} -> (Ord -> s -> t -> Ord) -> s -> t -> Ord
 lim2 f x = lim1 (\(p : Ord) -> f p x)
-}

 limx1 : {s : Set} -> (Nat -> s -> Ord) -> s -> Ord
 limx1 f x = Lim (\(p : Nat) -> f p x)

 limx2 : {s t : Set} -> (Nat -> s -> t -> Ord) -> s -> t -> Ord
 limx2 f x = limx1 (\(p : Nat) -> f p x)

 Lim1 : {s : Set} -> (Ord -> s -> Ord) -> s -> Ord
 Lim1 f x = Lim (\(p : Nat) -> f (OrdNat p) x)

 Lim2 : {s t : Set} -> (Ord -> s -> t -> Ord) -> s -> t -> Ord
 Lim2 f x = Lim1 (\(p : Ord) -> f p x)
 
 ford : Nat -> Set
 ford O = Ord
 ford (1+ n) = ford n -> ford n

 lim1 : (Nat -> Ord -> Ord) -> Ord -> Ord
 lim1 f x = Lim (\(p : Nat) -> f p x)

 lim2 : (Nat -> (Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 lim2 f x = lim1 (\(p : Nat) -> f p x)

 limn : (n : Nat) -> (Nat -> ford n) -> ford n
 limn O f = Lim f
 limn (1+ p) f = \x -> limn p (\q -> f q x)

{-
let rec limit = function
	Zero -> lim |
	Suc n -> function f -> function x -> limit n (function p -> f p x);;

let H'0 = H';;
let rec H'1 phi f x = lim1 (function y -> phi (rep x f y));;
let rec H'2 phi f x = lim2 (function y -> phi (rep x f y));;

let omega_power_omega_power_omega' =
	H'2 I (H'1 I) (H'0 I) suc Zero;;

H'0 : ('a -> Ord) -> ('a -> 'a) -> 'a -> Ord = <fun>
H'1 : ('a -> 'b -> Ord) -> ('a -> 'a) -> 'a -> 'b -> Ord = <fun>
H'2 : ('a -> 'b -> 'c -> Ord) -> ('a -> 'a) -> 'a -> 'b -> 'c -> Ord = <fun>
omega_power_omega_power_omega' : Ord = Lim <fun>

-}

 H'0 : {s : Set} -> (s -> Ord) -> (s -> s) -> s -> Ord
 H'0 = H'

 H'1 : {s t : Set} -> (s -> t -> Ord) -> (s -> s) -> s -> t -> Ord
 H'1 phi f x = limx1 (\(y : Nat) -> phi (rep x f y))

 -- H'1o : {s t : Set} -> (s -> t -> Ord) -> (s -> s) -> s -> t -> Ord
 -- H'1o phi f x = Lim1 (\(y : Ord) -> phi (Rep x f y))

 H'2 : {s t u : Set} -> (s -> t -> u -> Ord) -> (s -> s) -> s -> t -> u -> Ord
 H'2  phi f x = limx2 (\(y : Nat) -> phi (rep x f y))

 H0 = H
 
{-
let H1 f g = lim1 (rep g f);;   (* g x U f g x U f (f g) x U ... *)
let H2 f g = lim2 (rep g f);;

H0 : (Ord -> Ord) -> Ord -> Ord = <fun>
H1 : (('a -> Ord) -> 'a -> Ord) -> ('a -> Ord) -> 'a -> Ord = <fun>
H2 :
 (('a -> 'b -> Ord) -> 'a -> 'b -> Ord) ->
 ('a -> 'b -> Ord) -> 'a -> 'b -> Ord = <fun>
-}

 Hx1 : {s : Set} -> ((s -> Ord) -> s -> Ord) -> (s -> Ord) -> s -> Ord 
 Hx1 f g = limx1 (rep g f)

 Hx2 : {s t : Set} -> ((s -> t -> Ord) -> s -> t -> Ord) -> (s -> t -> Ord) -> s -> t -> Ord
 Hx2 f g = limx2 (rep g f)

 H1 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord 
 H1 f g = lim1 (rep g f)

 H2 : (((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord) -> ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 H2 f g = lim2 (rep g f)

 Hn : (n : Nat) -> ford (1+ (1+ n))
 Hn n f g = limn n (rep g f)

 H''1 : (f : (Ord -> Ord) -> (Ord -> Ord)) -> (g : Ord -> Ord) -> (x : Ord) -> Ord 
 -- H''1 f g x = Lim (\(n : Nat) -> repeat _ n f g x)
 H''1 f g x = Lim (\(n : Nat) -> rep g f n x)

{-
 omega_power_omega : Ord
 omega_power_omega = H1 H suc Zero

 omega_power_omega_power_omega : Ord
 omega_power_omega_power_omega = H2 H1 H suc Zero
-}

 OmegaPowerOmega : Ord
 OmegaPowerOmega = H1 H Suc Zero

 OmegaPowerOmegaPowerOmega : Ord
 OmegaPowerOmegaPowerOmega = H2 H1 H Suc Zero

 OmegaPowerOmegaPowerOmega' = (Hn (1+ (1+ O))) (Hn (1+ O)) (Hn O) Suc Zero

 OmegaPowerOmegaPowerOmega'' = (Hn _) (Hn _) (Hn _) Suc Zero

{- This does not seem to work:
 H'' = Hn _
 OmegaPowerOmegaPowerOmega''' = H'' H'' H'' Suc Zero
-}

 data List (t : Set) : Set where
  Nil : List t
  Cons : t -> List t -> List t

 ApplyList : {t u : Set} -> (List t) -> u -> (t -> u -> u) -> u
 ApplyList Nil a f = a
 ApplyList (Cons x l) a f = f x (ApplyList l a f)

 data HGList (t : Set) (f : Set -> Set) : Set where
  HGNil : HGList t f
  HGCons : t -> HGList (f t) f -> HGList t f

 -- Hseq n p = (Hn n+p) ... (Hn p)
 Hseq : (n : Nat) -> (p : Nat) -> ford (1+ (1+ p))
 Hseq O p = Hn p
 Hseq (1+ n) p = Hseq n (1+ p) (Hn p)

 Eps0 : Ord
 Eps0 = Lim (\(n : Nat) -> Hseq n O Suc Zero)

 seq : (h : (n : Nat) -> ford (1+ (1+ n))) -> (n : Nat) -> (p : Nat) -> ford (1+ (1+ p))
 seq h O p = h p
 seq h (1+ n) p = seq h n (1+ p) (h p)

 Eps0' : Ord
 Eps0' = Lim (\(n : Nat) -> seq Hn n O Suc Zero)

 R1 : ((n : Nat) -> ford (1+ (1+ n))) -> (Ord -> Ord) -> Ord -> Ord
 R1 h s z = Lim (\(n : Nat) -> seq h n O s z)
 
 Eps0'' : Ord
 Eps0'' = R1 Hn Suc Zero

 -- Hseq' n  = (Hn _) ... (Hn _)
 Hseq' : {p : Nat} -> Nat -> ford (1+ (1+ p))
 Hseq' O = Hn _
 Hseq' (1+ n) = (Hseq' n) (Hn _) 

 Eps0''' : Ord
 Eps0''' = Lim (\(n : Nat) -> Hseq' n Suc Zero)

 seq' : {p : Nat} -> (h : (n : Nat) -> ford (1+ (1+ n))) -> (n : Nat) -> ford (1+ (1+ p))
 seq' h O = h _
 seq' h (1+ n) = seq' h n (h _)
 
 Eps0'''' : Ord
 Eps0'''' = Lim (\(n : Nat) -> seq' Hn n Suc Zero)

 R1' : ((n : Nat) -> ford (1+ (1+ n))) -> (Ord -> Ord) -> Ord -> Ord
 R1' h s z = Lim (\(n : Nat) -> seq' h n s z)

 -- R11' : ((n : Nat) -> ford (1+ (1+ (1+ n)))) -> ford (1+ (1+ (1+ O)))
 -- R11' h1 h0 s z = Lim (\(n : Nat) -> seq' h1 h0 n s z)

 Eps0''''' : Ord
 Eps0''''' = R1' Hn Suc Zero

 SEps0 : Ord
 SEps0 = Suc (R1' Hn Suc Zero)

 HSEps0 : Ord
 HSEps0 = Hn _ Suc (R1' Hn Suc Zero)

 R1HSEps0 : Ord
 R1HSEps0 = R1' Hn Suc (R1' Hn Suc Zero)

 HR1HSZ : Ord
 HR1HSZ = Hn _ (R1' Hn Suc) Zero

 R1HR1HSZ : Ord
 R1HR1HSZ = R1' Hn (R1' Hn Suc) Zero

 HR1HSZ' : Ord
 HR1HSZ' = Hn _ (R1' Hn) Suc Zero

 HHR1HSZ : Ord
 HHR1HSZ = Hn _ (Hn _) (R1' Hn) Suc Zero
 
 -- R1HR1HSZ' : Ord
 -- R1HR1HSZ' = R1' Hn (R1' Hn) Suc Zero

 -- R1R1HSZ : Ord
 -- R1R1HSZ = R1' (R1' Hn) Suc Zero

 -- HR1HSZ : Ord
 -- HR1HSZ = (Hn _) R1' (Hn _) Suc Zero
 -- HR1HSZ = Hn (1+ (1+ O)) R1' (Hn O) Suc Zero

 f0 : Ord -> Ord
 f0 x = op x x x
 
 Meta : (Ord -> Ord) -> Ord -> Ord -> Ord
 Meta f Zero y = f y
 Meta f (Suc x) y = Rep y (Meta f x) y
 Meta f (Lim phi) y = Lim (\(x : Nat) -> Meta f (phi x) y)

 META0 : (Ord -> Ord) -> Ord -> Ord -> Ord
 META0 s z Zero = z
 META0 s z (Suc x) = s (META0 s z x)
 META0 s z (Lim phi) = Lim (\(x : Nat) -> META0 s z (phi x))

 META : (t : Set) -> ((t -> Ord) -> t -> Ord) -> (t -> Ord) -> Ord -> t -> Ord
 META t s z Zero = z
 META t s z (Suc x) = s (META t s z x)
 META t s z (Lim phi) = \(x : t) -> Lim (\(y : Nat) -> META t s z (phi y) x)

 META1 = META

 META2 : (t1 t2 : Set) -> ((t1 -> t2 -> Ord) -> t1 -> t2 -> Ord) -> (t1 -> t2 -> Ord) -> Ord -> t1 -> t2 -> Ord
 META2 t1 t2 s z Zero = z
 META2 t1 t2 s z (Suc x) = s (META2 t1 t2 s z x)
 META2 t1 t2 s z (Lim phi) = \(x1 : t1) -> \(x2 : t2) -> Lim (\(y : Nat) -> META2 t1 t2 s z (phi y) x1 x2)

 META3 : (t1 t2 t3 : Set) -> ((t1 -> t2 -> t3 -> Ord) -> t1 -> t2 -> t3 -> Ord) -> (t1 -> t2 -> t3 -> Ord) -> Ord -> t1 -> t2 -> t3 -> Ord
 META3 t1 t2 t3 s z Zero = z
 META3 t1 t2 t3 s z (Suc x) = s (META3 t1 t2 t3 s z x)
 META3 t1 t2 t3 s z (Lim phi) = \(x1 : t1) -> \(x2 : t2) -> \(x3 : t3) -> Lim (\(y : Nat) -> META3 t1 t2 t3 s z (phi y) x1 x2 x3)

 m0 = omega

 m1 = f0
 
 m2 : (Ord -> Ord) -> Ord -> Ord
 m2 x y = Rep omega (Meta x y) omega

 m3 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 m3 f1 f x = META _ f1 f x x

 m30 : Ord
 m30 = m3 m2 m1 m0

{-

let f0 x = op x x x;;

let rec Meta f = function
	Zero -> f |
	Suc x -> (function y -> Rep y (Meta f x) y) |
	Lim phi -> (function x -> Lim (function y -> Meta f (phi y) x));;

let rec META0 s z = function
	Zero -> z |
	Suc x -> s (META0 s z x) |
	Lim phi -> Lim (function x -> META0 s z (phi x));;

let rec META s z = function
	Zero -> z |
	Suc x -> s (META s z x) |
	Lim phi -> (function x -> Lim (function y -> META s z (phi y) x));;

let META1 = META;;

let rec META2 s z = function
	Zero -> z |
	Suc x -> s (META2 s z x) |
	Lim phi -> (function x1 -> function x2 -> 
			Lim (function y -> META2 s z (phi y) x1 x2));;

let rec META3 s z = function
	Zero -> z |
	Suc x -> s (META3 s z x) |
	Lim phi -> (function x1 -> function x2 -> function x3 ->
			Lim (function y -> META3 s z (phi y) x1 x2 x3));;

let m0 = omega;;

let m1 = f0;;

let m2 x y = Rep omega (Meta x y) omega;;

let m3 f1 f x = META f1 f x x;;

let m3_0 = m3 m2 m1 m0;;

(*

omega = H suc 0
omega * 2 = H suc (H suc 0)
omega ** 2 = H (H suc) 0
omega ** omega = H H suc 0
epsilon 0 = R1 H suc 0
epsilon 0 + 1 = suc (R1 H suc 0)
epsilon 0 * 2 = R1 H suc (R1 H suc 0)
epsilon 0 ** 2 = R1 H (R1 H suc) 0
epsilon 0 ** omega = H (R1 H) suc 0
epsilon 0 ** epsilon 0 = R1 H (R1 H) suc 0
epsilon 1 = R1 (R1 H) suc 0
epsilon omega = H R1 H suc 0
epsilon epsilon omega = R1 H R1 H suc 0

op 0 omega omega = op 1 2 omega = omega * 2 = H suc (H suc 0)
op 1 omega omega = op 2 2 omega = omega ** 2 = H (H suc) 0
op 2 omega omega = op 3 2 omega = omega ** omega = H H suc 0
op 3 omega omega = op 4 2 omega = epsilon 0 = R1 H suc 0
op 4 omega omega = op 5 2 omega = epsilon omega = H R1 H suc 0

op 4 omega omega = op (3+1) (Lim I) omega = Lim (x -> op 4 x omega)
	op 4 2 omega = epsilon 0
	op 4 3 omega = op (3+1) (2+1) omega = op 3 omega (op 4 2 omega)
		= op 3 omega (epsilon 0) = epsilon 0 *** omega 
		= epsilon 1 = R1 (R1 H) suc 0
	...
	op 4 omega omega = epsilon omega = H R1 H suc 0

META s z x = (0->z, suc->s) x
	META s z 0 = z
	META s z (suc x) = s (META s z x)
	META s z (Lim f) = Lim (x->META s z (f x))

x -f-> f x -> f (f x) -> ... -> meta0 f x = META f x x
0      1      2                 x

f -meta0-> meta0 f -> meta0 (meta0 f) -> ... -> META meta0 f x
f x        meta0 f x  meta0 (meta0 f) x         META meta0 f x x
0          1          2                         x

meta 0 f x = [META %% % %] f x = META f x x
meta 1 f x = [META [META %% % %] %% % %] f x = META (meta 0) f x x
...
meta x f x

f -> (x->meta x f x)
 
*)

-}

 meta0 : (Ord -> Ord) -> Ord -> Ord
 meta0 f x = META0 f x x

 meta1 : (Ord -> Ord) -> Ord -> Ord
 meta1 f x = META1 _ meta0 f x x

 meta2 : (Ord -> Ord) -> Ord -> Ord
 meta2 f x = META1 _ meta1 f x x

 meta : Ord -> (Ord -> Ord) -> Ord -> Ord
 meta Zero f x = meta0 f x
 meta (Suc n) f x = META1 _ (meta n) f x x
 meta (Lim phi) f x = Lim (\(y : Nat) -> meta (phi y) f x)

 metan : ((Ord -> Ord) -> Ord -> Ord) -> Ord -> (Ord -> Ord) -> Ord -> Ord
 metan m Zero f x = m f x
 metan m (Suc n) f x = META1 _ (meta n) f x x
 metan m (Lim phi) f x = Lim (\(y : Nat) -> meta (phi y) f x)

 prime0 : ((Ord -> Ord) -> Ord -> Ord) -> Ord -> (Ord -> Ord) -> Ord -> Ord
 prime0 m Zero f x = m f x
 prime0 m (Suc n) f x = metan (prime0 m n) x f x
 prime0 m (Lim phi) f x = Lim (\(y : Nat) -> prime0 m (phi y) f x)

 prim0 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 prim0 m = prime0 m (Suc Zero)

 prim1 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 prim1 m f x = META2 _ _ prim0 m x f x

 prim2 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 prim2 m f x = META2 _ _ prim1 m x f x

 prim3 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 prim3 m f x = META2 _ _ prim2 m x f x

 prim : Ord -> ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 prim Zero m f x = prim0 m f x
 prim (Suc n) m f x = META2 _ _ (prim n) m x f x
 prim (Lim phi) m f x = Lim (\(y : Nat) -> prim (phi y) m f x)

 prim' : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord 
 prim' m f x = prim x m f x

{-

let meta0 f x = META0 f x x;;
let meta1 f x = META1 meta0 f x x;;
let meta2 f x = META1 meta1 f x x;; 

let rec meta = function
	Zero -> meta0 |
	Suc n -> (function f -> function x -> META1 (meta n) f x x) |
	Lim phi -> (function f -> function x -> 
		Lim (function y -> meta (phi y) f x));;

let meta' f x = meta x f x;;

let rec metan m = function
	Zero -> m |
	Suc n -> (function f -> function x -> META1 (metan m n) f x x) |
	Lim phi -> (function f -> function x -> Lim (function y ->
		metan m (phi y) f x));;

let rec prime0 m = function
	Zero -> m |
	Suc n -> (function f -> function x -> metan (prime0 m n) x f x) |
	Lim phi -> (function f -> function x -> Lim (function y -> 
		prime0 m (phi y)f x));;

(*
let prime1 meta0 f x = META2 (function m -> prime0 m x) meta0 x f x;; 
let prime2 meta0 f x = META2 prime1 meta0 x f x;;
let prime3 meta0 f x = META2 prime2 meta0 x f x;;
*)

let rec prim0 m = prime0 m (Suc Zero);;

let prim1 m f x = META2 prim0 m x f x;; 
let prim2 m f x = META2 prim1 m x f x;;
let prim3 m f x = META2 prim2 m x f x;;

let rec prim = function
	Zero -> prim0 |
	Suc n -> (function m -> function f -> function x ->
		META2 (prim n) m x f x) | 
	Lim phi -> (function m -> function f -> function x ->
		Lim (function y -> prim (phi y) m f x));;

let prim' m f x = prim x m f x;;
(*  O3    O2    O1 O 
    prim' meta0 f0 omega 
=   M3    M2    M1 M0 = M3_0
    
    *)

(*

let prim'' m f x = prim' x m f x;;

let second p m f x = p x m f x;;

let prim'1 = second prim;;
let prim''1 = second (second prim);;

let M3 = META3 second prim;;


META1 (meta n) f x x
META2 (prim n) m x f x
META3 (second n) p x m f x

meta = metan meta0
prim = primn prim0

prim0 m f x = metan m x f x
second0 p m f x = primn p x m f x

primn p 0 = p
primn p (n+1) m f x = META2 (primn p n_ m x f x

second 0 = second0
second (n+1) p m f x = META3 (second n) p x m f x
second (Lim phi) p m f x = Lim (y->second (phi y) p m f x

*)
-}

 primn : {t : Set} -> ((t -> Ord -> Ord) -> t -> Ord -> Ord) -> Ord -> (t -> Ord -> Ord) -> t -> Ord -> Ord
 primn p Zero m f x = p m f x
 primn p (Suc n) m f x = META2 _ _ (primn p n) m x f x
 primn p (Lim phi) m f x = Lim (\(y : Nat) -> primn p (phi y) m f x)

 second0 : {t : Set} -> ((t -> Ord -> Ord) -> t -> Ord -> Ord) -> (t -> Ord -> Ord) -> t -> Ord -> Ord
 second0 p m f x = primn p x m f x

 second : {t : Set} -> Ord -> ((t -> Ord -> Ord) -> t -> Ord -> Ord) -> (t -> Ord -> Ord) -> t -> Ord -> Ord
 second Zero p m f x = second0 p m f x
 second (Suc n) p m f x = META3 _ _ _ (second n) p x m f x
 second (Lim phi) p m f x = Lim (\(y : Nat) -> second (phi y) p m f x)

 secondn : {t u : Set} -> ((t -> u -> Ord -> Ord) -> t -> u -> Ord -> Ord) -> Ord -> (t -> u -> Ord -> Ord) -> t -> u -> Ord -> Ord
 secondn s Zero p m f x = s p m f x
 secondn s (Suc n) p m f x = META3 _ _ _ (secondn s n) p x m f x
 secondn s (Lim phi) p m f x = Lim (\(y : Nat) -> secondn s (phi y) p m f x)

 ter0 : {t u : Set} -> ((t -> u -> Ord -> Ord) -> t -> u -> Ord -> Ord) -> (t -> u -> Ord -> Ord) -> t -> u -> Ord -> Ord
 ter0 s p m f x = secondn s x p m f x

 ord6 : Ord
 ord6 = ter0 second0 prim0 meta0 f0 omega

{-
let rec primn p = function
	Zero -> p |
	Suc n -> (function m -> function f -> function x ->
		META2 (primn p n) m x f x) |  
	Lim phi -> (function m -> function f -> function x ->
		Lim (function y -> primn p (phi y) m f x));;

let second0 p m f x = primn p x m f x;;

let rec second = function
	Zero -> second0 |
	Suc n -> (function p -> function m -> function f -> function x ->
		META3 (second n) p x m f x) |
	Lim phi -> (function p -> function m -> function f -> function x ->
		Lim (function y -> second (phi y) p m f x));;

let rec secondn s = function
	Zero -> s |
	Suc n -> (function p -> function m -> function f -> function x ->
		META3 (secondn s n) p x m f x) |
	Lim phi -> (function p -> function m -> function f -> function x ->
		Lim (function y -> secondn s (phi y) p m f x));;

let ter0 s p m f x = secondn s x p m f x;;

let ord6 = ter0 second0 prim0 meta0 f0 omega;;

-}

 fxp : {t : Set} -> (t -> t) -> t -> Nat -> t
 fxp f x O = x
 fxp f x (1+ n) = fxp f (f x) n

 ordofint : Nat -> Ord
 ordofint n = fxp Suc Zero n

 gamma : Ord -> Nat -> Nat
 gamma Zero n = O
 gamma (Suc x) n = 1+ (gamma x n)
 gamma (Lim phi) n = gamma (phi n) n  

 lambda : Ord -> Nat -> Nat
 lambda Zero n = n
 lambda (Suc x) n = lambda x (1+ n)
 lambda (Lim phi) n = lambda (phi n) n

{-

let rec fxp f x p = (if (p = 0) then x else (fxp f (f x) (p - 1)));;

let ord_of_int = fxp suc Zero;; 

let rec gamma x n = match x with
	Zero -> 0 |
	Suc x -> ((gamma x n) + 1) |
	Lim phi -> (gamma (phi (ord_of_int n)) n);;

let rec lambda x n = match x with
	Zero -> n |
	Suc x -> (lambda x (n + 1)) |
	Lim phi -> (lambda (phi (ord_of_int n)) n);;

(* lambda epsilon0 omega = gamma eta0 omega = eta0 *)

-}

 lambda' : Ord -> Nat -> Nat
 lambda' Zero n = n
 lambda' (Suc x) n = lambda' x (1+ n)
 lambda' (Lim phi) n = lambda' (phi n) n 

{-

let rec lambda' x n = match x with
	Zero -> n |
	Suc x -> (lambda' x (Suc n)) |
	Lim phi -> (lambda' (phi n) n);;

(* let eta0 = lambda' epsilon0 omega;; *)

f0 : Ord -> Ord = <fun>
Meta : (Ord -> Ord) -> Ord -> Ord -> Ord = <fun>
META0 : (Ord -> Ord) -> Ord -> Ord -> Ord = <fun>
META : (('a -> Ord) -> 'a -> Ord) -> ('a -> Ord) -> Ord -> 'a -> Ord = <fun>
META1 : (('a -> Ord) -> 'a -> Ord) -> ('a -> Ord) -> Ord -> 'a -> Ord = <fun>
META2 :
 (('a -> 'b -> Ord) -> 'a -> 'b -> Ord) ->
 ('a -> 'b -> Ord) -> Ord -> 'a -> 'b -> Ord = <fun>
META3 :
 (('a -> 'b -> 'c -> Ord) -> 'a -> 'b -> 'c -> Ord) ->
 ('a -> 'b -> 'c -> Ord) -> Ord -> 'a -> 'b -> 'c -> Ord = <fun>
m0 : Ord = Lim <fun>
m1 : Ord -> Ord = <fun>
m2 : (Ord -> Ord) -> Ord -> Ord = <fun>
m3 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord = <fun>
m3_0 : Ord = Lim <fun>
meta0 : (Ord -> Ord) -> Ord -> Ord = <fun>
meta1 : (Ord -> Ord) -> Ord -> Ord = <fun>
meta2 : (Ord -> Ord) -> Ord -> Ord = <fun>
meta : Ord -> (Ord -> Ord) -> Ord -> Ord = <fun>
meta' : (Ord -> Ord) -> Ord -> Ord = <fun>
metan : ((Ord -> Ord) -> Ord -> Ord) -> Ord -> (Ord -> Ord) -> Ord -> Ord =
 <fun>
prime0 : ((Ord -> Ord) -> Ord -> Ord) -> Ord -> (Ord -> Ord) -> Ord -> Ord =
 <fun>
prim0 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord = <fun>
prim1 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord = <fun>
prim2 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord = <fun>
prim3 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord = <fun>
prim : Ord -> ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord =
 <fun>
prim' : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord = <fun>
primn :
 (('a -> Ord -> Ord) -> 'a -> Ord -> Ord) ->
 Ord -> ('a -> Ord -> Ord) -> 'a -> Ord -> Ord = <fun>
second0 :
 (('a -> Ord -> Ord) -> 'a -> Ord -> Ord) ->
 ('a -> Ord -> Ord) -> 'a -> Ord -> Ord = <fun>
second :
 Ord ->
 (('a -> Ord -> Ord) -> 'a -> Ord -> Ord) ->
 ('a -> Ord -> Ord) -> 'a -> Ord -> Ord = <fun>
secondn :
 (('a -> 'b -> Ord -> Ord) -> 'a -> 'b -> Ord -> Ord) ->
 Ord -> ('a -> 'b -> Ord -> Ord) -> 'a -> 'b -> Ord -> Ord = <fun>
ter0 :
 (('a -> 'b -> Ord -> Ord) -> 'a -> 'b -> Ord -> Ord) ->
 ('a -> 'b -> Ord -> Ord) -> 'a -> 'b -> Ord -> Ord = <fun>
ord6 : Ord = Lim <fun>
fxp : ('a -> 'a) -> 'a -> int -> 'a = <fun>
ord_of_int : int -> Ord = <fun>
gamma : Ord -> int -> int = <fun>
lambda : Ord -> int -> int = <fun>
lambda' : Ord -> Ord -> Ord = <fun>

-}


 
