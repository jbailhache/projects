
Inductive ord : Type :=
 | zero : ord
 | suc : ord -> ord
 | lim : (nat -> ord) -> ord.

Fixpoint ordofnat (n:nat) : ord :=
 match n with
  | O => zero
  | S p => suc (ordofnat p)
 end.

Definition w := lim ordofnat.

Fixpoint repeat (a:Type) (n:nat) (f:a->a) (x:a) : a := 
 match n with
  | O => x
  | S p => repeat a p f (f x)
 end. 

Definition plusw (x:ord) : ord := lim (fun n => repeat _ n suc x).

Definition w' := plusw zero.

Definition wx2 := plusw (plusw zero).

Definition wp2 := lim (fun n => repeat _ n plusw zero).

Definition pluswp2 (x:ord) := lim (fun n => repeat _ n plusw x).

Definition H0 (f:ord->ord) (x:ord) : ord := lim (fun n => repeat _ n f x).

Definition w'' := H0 suc zero.

Definition H1 (f:(ord->ord)->(ord->ord)) (g:ord->ord) x:ord :=
 lim (fun n => repeat _ n f g x).

Definition wpw := H1 H0 suc zero.

Fixpoint ford (n:nat) : Type :=
 match n with
  | O => ord
  | S p => (ford p) -> (ford p)
 end.

(*
Fixpoint Lim (n:nat) (f:nat->(ford n)) : ford n :=
 match n with
  | O => lim f
  | S p => (fun x => Lim p (fun q => f q x))
 end.

Fixpoint Lim (n:nat) : (nat->_) -> _ :=
 match n with
  | O => (fun f => lim f)
  | S p => (fun f => fun x => Lim p (fun q => f q x))
 end.

Fixpoint Lim (n:nat) :=
 match n with
  | O => (fun f => lim f)
  | S p => (fun f => fun x => Lim p (fun q => f q x))
 end.
*)

(*
Definition H (n:nat) (f:ford(n+1)) (x:ford n) : ford n :=
 Lim n (fun p => repeat _ p f x).
*)

Definition lim1 f (x:ord) := lim (fun p => f p x).
Definition lim2 f (x:ford 1) := lim1 (fun p => f p x).

(*
Fixpoint Lim (n:nat) := 
 match n with
  | O => (fun f => lim f)
  | S p => (fun f (x: ford p) => Lim p (fun p => f p x))
 end.
*)

 

