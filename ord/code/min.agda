--#include "Amenities.agda"

package Relations ( A :: Set) (R :: A -> Pow A) where

  reflexive :: Set
    = (a :: A)-> R a a

  transitive :: Set
    = (a, b, c :: A)-> 
        a `R` b -> b `R` c -> a `R` c

  symmetric :: Set
    =  (a, b :: A) -> 
         a `R` b -> b `R` a

  precat :: Set   -- quasiorder
    = reflexive `and` transitive

  eqrel :: Set
    = precat `and` symmetric
  
  package Bounds (I :: Set) (as :: I -> A) where

    Upper (b :: A) :: Set 
      = (i :: I)-> as i `R` b

    Lower (b :: A) :: Set 
      = (i :: I)-> b `R` as i

    Least (P :: A -> Set) (a :: A) :: Set
      = P a `and` (c :: A)-> P c -> a `R` c

    Greatest (P :: A -> Set) (a :: A) :: Set
      = P a `and` (c :: A)-> P c -> c `R` a

    LeastUpper (b :: A) :: Set
      = Least Upper b 

    GreatestLower (b :: A) :: Set
      = Greatest Lower b 

    Infimum :: Set 
      = sig form :: A
            prop :: LeastUpper form

    Supremum :: Set
      = sig form :: A
            prop :: GreatestLower form

  inf_struct (I :: Set) :: Set
      = sig 
          pc    :: precat
          inf    :: (I -> A) -> A
          infp   :: (as :: I -> A) -> 
                    (Bounds I as).GreatestLower (inf as) 

  sup_struct (I :: Set) :: Set
      = sig 
          pc    :: precat
          sup    :: (I -> A) -> A
          supp  :: (as :: I -> A) -> 
                    (Bounds I as).LeastUpper (sup as) 

package Relative0 (FS :: Fam Set) where

  set :: Set = FS.I
  el  :: set -> Set = FS.i 

  fam (A :: Set) :: Set 
    = sig u :: set
          t :: el u -> A

  fam_map (A, B :: Set) (f :: A -> B)
    :: fam A -> fam B
    = \(h::fam A) -> 
      struct u = h.u
             t = \(x::el u) -> f (h.t x)

  fam2Fam (A :: Set) :: fam A -> Fam A
    = \(h::fam A) -> 
      struct  I = el h.u
              i = h.t 

  pow (A :: Set) :: Set
    = A -> set

  pow_map (A, B :: Set) (f :: A -> B)
    :: pow B -> pow A
    = \(X :: pow B) -> 
      \(a :: A) -> 
      X (f a)

  pow2Pow (A :: Set) :: pow A -> Pow A
    = \(h::pow A) -> \(a::A) -> el (h a)

  {- Now we focus on the predicates over a
     single set. 
  -}
  package Predicates (A :: Set) where

    pred :: Set = pow A
    pt   :: Set = op pred

    op1  :: Set = op A 
    op2  :: Set = A -> op A 

    eps (a :: A) (P :: pred) :: Set 
       = el (P a)

    subset (P, Q :: pred) :: Set
       = (a :: A)-> 
           a `eps` P -> a `eps` Q

    subpt (F, G :: pt) :: Set
       = (P :: pred)-> F P `subset` G P

    pcpred :: (Relations pred subset).precat
       = struct 

           fst = \(a::pred) -> 
                 \(a'::A) -> 
                 \(h::eps a' a) -> 
                 h

           snd = \(a,b,c::pred) -> 
                 \(h::subset a b) -> 
                 \(h'::subset b c) -> 
                 \(x::A) -> 
                 \(xa::eps x a) -> 
                 h' x (h x xa)

    pcpt :: (Relations pt subpt).precat
       = struct 

           fst = \(F::pt) -> \(P::pred) -> pcpred.fst (F P) 

           snd = \(F,G,H::pt) -> 
                 \(h::subpt F G) ->
                 \(h'::subpt G H) ->
                 \(P::pred) -> 
                 \(a::A) -> 
                 \(fpa::eps a (F P)) ->
                 pcpred.snd (F P) (G P) (H P) 
                            (h P) (h' P) 
                            a fpa

    pred_map :: op1 -> pt 
       = pow_map A A 

    mph (f :: op1) (P, Q :: pred) :: Set 
       = P `subset` (f `pred_map` Q)

    monotone (F :: pt) 
            :: Set
       = (P, Q :: pred) -> 
            P `subset` Q  -> F P `subset` F Q

    observation1 
       (f :: op1) :: monotone (pred_map f)
       = \(P,Q::pred) -> 
         \(h::subset P Q) ->
         \(a::A) -> 
         \(pfa::eps a (pred_map f P)) ->
         h (f a) pfa

    tofam (N :: Set) (ps :: N -> pred) :: Fam pred
       = struct { I = N ; i = ps ; }

    infs (N :: Set)
       :: Set
       = (ps :: N -> pred)-> 
            ((Relations pred subset).Bounds N ps).Infimum

    package Progressivity (F :: pt) (mF :: monotone F) where

      prog (P :: pred) :: Set
        = F P `subset` P

      pprog (G :: pt) :: Set
        = (P :: pred) -> prog P -> prog (G P)

      acc (a :: A) :: Set
        = (X :: pred) -> prog X -> a `eps` X 

      protolens :: Set
        = Si pt pprog

      {- UNUSED: But this is
         what is really going on.
      -} 
      lens' (f :: op1) :: Set
        = sig pt :: pt
              pp :: pprog pt
              pm :: (X :: pred) -> 
                    prog X -> mph f (pt X) X

      {- The official definition. -}
      lens (f :: op1) :: Set
        = Si protolens (\(h::protolens) ->
              (X::pred) -> prog X -> 
                mph f (h.fst X) X)

      {- A lens for a function is a particular
         way of proving that the accessible
         elements for some functor are closed
         under a given function. 
      -}
      lens2acc (f :: op1) (l :: lens f) 
               (a :: A) (pa :: acc a) 
        :: acc (f a)
        = let -- the following is just plumbing.
              pl :: protolens = l.fst
              pt :: pt = pl.fst 
              pp :: pprog pt = pl.snd 
              pm :: (X :: pred) -> 
                       prog X -> mph f (pt X) X 
                 = l.snd
          in \(X :: pred) -> 
             \(pX :: prog X) -> 
             pm X pX a (pa (pt X) (pp X pX))

{- Now a package where the universe is assumed to be 
   closed under cartesian products with a particular
   indexed set. This means that we can define intersections .-}

package nxtU (FS :: Fam Set) (G :: Set) where
  U :: Set = FS.I
  T :: U -> Set = FS.i

  mutual

    set :: Set = data t (x :: U) 
                    | pig (s :: G -> set)

    el :: set -> Set 
       = \(h::set) -> 
              case h of 
                 (t x) -> T x
                 (pig s) -> (x::G) -> el (s x)

  pig :: (G -> set) -> set = \(s :: G -> set) -> pig@set  s
  next :: Fam Set = struct {I = set; i = el;}

package Relative1 (FS :: Fam Set) (G :: Set) where

  open nxtU FS G 
    use set, el, pig, next

  open Relative0 next 
    use Predicates

  package Predicates2 (A :: Set) where
    open Predicates A 
         use pred, eps, subset,
             pt, subpt, 
             pcpred, pcpt

    ispred :: (Relations pred subset).inf_struct G
       = struct 

           pc = pcpred

           inf = \(Ps :: G -> pred) -> 
                   \(a::A) -> 
                   pig (\(g::G) -> Ps g a)

           infp = \(Ps :: G -> pred) -> 
                     struct 

                       fst = \(i::G) -> 
                             \(a::A) -> 
                             \(h::a `eps` inf Ps) -> 
                             h i

                       snd = \(c::pred) -> 
                             \(h::(i::G) -> c `subset` Ps i) ->
                             \(a::A) -> 
                             \(ca::el (c a)) -> 
                             \(i::G) -> 
                             h i a ca
    
    ispt :: (Relations pt subpt).inf_struct G 
       = struct

           pc = pcpt

           inf = \(Fs :: G -> pt) -> 
                   \(P::pred) -> 
                   ispred.inf (\(g::G) -> Fs g P) 

           infp = \(Fs :: G -> pt) ->
                   struct 

                     fst = \(i::G) -> 
                           \(P::pred) -> 
                           \(a::A) -> 
                           \(h::a `eps` inf Fs P) ->
                           h i

                     snd = \(C::pt) -> 
                           \(h::(i::G) -> C `subpt` Fs i) -> 
                           \(P::pred) -> 
                           \(a::A) -> 
                           \(ca :: a `eps` C P) -> 
                           \(i::G) -> 
h i P a ca
