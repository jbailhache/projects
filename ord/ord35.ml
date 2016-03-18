
type Ord = Zero | Suc of Ord | Lim of (Ord -> Ord);;

let suc x = Suc x;;
let lim f = Lim f;;

let One = Suc Zero;;

let I x = x;;

let omega = Lim I;;

let rec rep z s = function
	Zero -> z |
	Suc x -> s (rep z s x);;

let rec Rep z s = function
	Zero -> z |
	Suc x -> s (rep z s x) |
	Lim f -> Lim (function x -> rep z s (f x));;

let rec plus x y = match x with
	Zero -> y |
	Suc x1 -> Suc (plus x1 y) |
	Lim f -> Lim (function x1 -> plus (f x1) y);;

let rec times x y = match x with
	Zero -> Zero |
	Suc x1 -> plus y (times x1 y) |
	Lim f -> Lim (function x1 -> times (f x1) y);;

let rec power x y = match x with
	Zero -> One |
	Suc x1 -> times y (power x1 y) |
	Lim f -> Lim (function x1 -> power (f x1) y);;

let rec hpower x y = match x with
	Zero -> One |
	Suc x1 -> power y (hpower x1 y) |
	Lim f -> Lim (function x1 -> hpower (f x1) y);;

let plus' a b = Rep b suc a;;

let times' a b = rep Zero (plus' b) a;;

let power' a b = rep (Suc Zero) (times' b) a;;

let rec op = function
	Zero -> plus |
	Suc Zero -> times |
	Suc n -> (function x -> function y ->
		match x with
			Zero -> One |
			Suc Zero -> y |
			Suc x1 -> op n y (op (Suc n) x1 y) |
			Lim f -> Lim (function x1 -> op (Suc n) (f x1) y)) |
	Lim f -> (function x -> function y ->
			Lim (function n1 -> op n1 x y));;

let epsilon0 = Lim (rep Zero (function x -> power x omega));;

let epsilon0' = hpower omega omega;;

let epsilon0'' = op (Suc (Suc (Suc (Suc Zero)))) (Suc (Suc Zero)) omega;;

let H f x = Lim (rep x f);;

let B f g x = f (g x);;

let H' phi f x = Lim (function y -> phi (rep x f y));;

(*
	limit 0 f = (f 0) U (f 1) U ...
	limit 1 f x = (f 0 x) U ...
		= limit 0 (\p. f p x)

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
*)

let lim1 f x = Lim (function p -> f p x);;
let lim2 f x = lim1 (function p -> f p x);;

(*
let rec limit = function
	Zero -> lim |
	Suc n -> function f -> function x -> limit n (function p -> f p x);;
*)

let H'0 = H';;
let rec H'1 phi f x = lim1 (function y -> phi (rep x f y));;
let rec H'2 phi f x = lim2 (function y -> phi (rep x f y));;

let omega_power_omega_power_omega' =
	H'2 I (H'1 I) (H'0 I) suc Zero;;

let H0 = H;;
(*
let rec H1 f x = lim1 (function y -> (rep x f y));;
let rec H2 f x = lim2 (function y -> (rep x f y));;
*)

let H1 f g = lim1 (rep g f);;   (* g x U f g x U f (f g) x U ... *)
let H2 f g = lim2 (rep g f);;

let omega_power_omega_power_omega =
	H2 H1 H suc Zero;;


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

let rec lambda' x n = match x with
	Zero -> n |
	Suc x -> (lambda' x (Suc n)) |
	Lim phi -> (lambda' (phi n) n);;

(* let eta0 = lambda' epsilon0 omega;; *)



