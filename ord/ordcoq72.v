
Inductive ord : Type :=
 | zero : ord
 | suc : ord -> ord
 | lim : (nat -> ord) -> ord.

Fixpoint ordofnat [n:nat] : ord :=
 Cases n of
    O => zero
  | (S p) => (suc (ordofnat p))
 end.

Definition w := (lim ordofnat).

Fixpoint repeat [a:Type] : (nat -> ((a->a) -> a)) 
 := [n:nat] [f:a->a] [x:a] 
 Cases n of
    O => x
  | (S p) => (repeat a p f (f x))
 end. 





