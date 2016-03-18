--#include "amenities.agda"
--#include "naturals.agda"
--#include "ordinals.agda"
--#include "nextU.agda"

{- This file, together with the files mentioned
   above, contains a proof of accessibility for Gamma0, 
   hence a sequence of proofs of accessibility, one for
   each term in the fundamental sequence for Gamma0.

   Each proof can be expressed 
   in a type theory in which there is a next universe
   operator (ie. an external sequence of universes).
   mapping a family of sets to the least family containing
   it as an internal subfamily which is closed under certain 
   operations (pi, sigma, Nat). 
   (Admittedly it needs close inspection to see this.)

   Closer inspection should reveal that we can construct
   a proof of accessibility for all notations, and 
   with a number of universes depending on the 
   levels to which the veblen hierarchy is nested.
   (But this is a little complex to set up.)

   The main result is called Corollary and is the
   last definition of the file.
-}

open Ordinals use  
    Ord, zero, limit, succ, 
    C, pd, 
    OpIt, OpItw, OpLim, 
    Nabla, 
    w, wexp, epsilon0, 
    v, veb, Gamma0,
    deriv, derivl

open Amenities 
   use N1, star,
       N0, efq, 
       Si, and, 
       op, op2, 
       Pow, Fam

open Naturals 
   use Nat, Seq, 
       It, Rec

package small( FS :: Fam Set ) where 

  Ot :: Set = Ord

  Us :: Set = FS.I
  Ts :: Us -> Set = FS.i

  {- small sets -}
  open UniverseOver Ot Us Ts use 
      set, el, 
      otcode, 
      pi, arr, 
      pin, piot

  Next :: Fam Set = struct 
                      I = set
                      i = el

  {- large sets -}
  open UniverseOver Ot set el use
      SET = set, 
      EL = el, 
      OT  = otcode, 
      ARR = arr,
      PI  = pi,
      PIN = pin,
      PIOT= piot,
      SI  = si, 
      AND = and

{------------ predicates ------------------}

  {- The type of real predicates -} 
  Pred :: Type  = Ot -> Set

  {- The Set of small predicates -}
  pred :: Set   = Ot -> set

  {- The Set of big predicates -}
  PRED :: Set   = Ot -> SET

  {- the representation of pred
     in SET.  We
     have EL PRED = pred; so PRED 
     represents or reflects pred. -}

  predcode :: SET = otcode@SET `ARR` u@SET

  {- that X is a subset of Y -} 
  subset (X, Y :: pred) :: set 
      = piot (\(a :: Ot)-> X a `arr` Y a)

  {- That "is a subset of" is transitive -}
  subsetTrans (p, q, r :: pred) 
    :: el ((p `subset` q) `arr` 
          ((q `subset` r) `arr` (p `subset` r)))
    = \(pq :: el (p `subset` q)) -> 
      \(qr :: el (q `subset` r)) -> 
      \(a :: Ot) -> 
      \(pa :: el (p a)) -> 
      qr a (pq a pa)

  {- That "is a subset of" is reflexive -}
  subsetRefl (p :: pred) 
    :: el (p `subset` p)
    = \(a :: Ot) -> \(pa :: el (p a)) -> pa

  {- Intersection of a sequence of predicates. -}
  capn (Xs :: Seq pred) :: pred
      = \(a :: Ot) -> pin (\(n :: Nat) -> Xs n a)

  {- That capn gives a lower bound for 
     sequences of predicates 
  -}
  capnLemOut (ps :: Seq pred)
    :: el (pin (\(n :: Nat) -> capn ps `subset` (ps n)))
    = \(n :: Nat) -> 
      \(a :: Ot) -> 
      \(psa :: el (capn ps a)) -> psa n

  {- That capn is a greatest lower bound 
     for sequences of predicates 
  -}
  capnLemIn (ps :: Seq pred) (q :: pred) 
    :: el (pin (\(n :: Nat) -> q `subset` (ps n)) 
           `arr` (q `subset` capn ps))
    = \(qps :: el (pin (\(n :: Nat) -> q `subset` ps n))) -> 
      \(a :: Ot) -> 
      \(qa :: el (q a)) -> 
      \(n :: Nat) ->
        qps n a qa

  {- Operation on a predicate which precomposes it with 
     an operation. -}
  sub (X :: pred) (f :: op Ot) :: pred
      = \(a :: Ot) -> X (f a)

  {- Property of a predicate that it is closed 
     under an operation -}
  clunder (X :: pred) (f :: op Ot) :: set
      = X `subset` (X `sub` f)

  {- predicate transformer induced by 
     a family of operations 
     = a binary operation -}
  clunder2 (X :: pred) (f :: op2 Ot) :: pred
      = \(a :: Ot) -> X `clunder` f a  

  {- PT induced by transition structure -}
  B :: pred -> pred
    = \(X :: pred) -> 
      \(a :: Ot) -> 
      case a of 
         (O) -> n1code@set
         (S a') -> X a'
         (L ls) -> pin (\(n :: Nat) -> X (ls n))

  {- That B is monotone. -}
  BM (p :: pred) (q :: pred) 
    :: el ((p `subset` q) `arr` (B p `subset` B q))
    = \(pq :: el (p `subset` q)) -> 
      \(a :: Ot) ->
       case a of 
         (O)    -> \(x :: N1) -> x
         (S a') -> pq a'
         (L ls) -> \(a' :: el (B p (limit ls))) -> 
                   \(n :: Nat) -> pq (ls n) (a' n)

  {- Progressivity of a predicate -}
  prog (X :: pred) :: set
    = piot (\(a :: Ot) -> B X a `arr` X a)

  Prog (X :: pred) :: Set 
    = el (prog X)

  B' :: PRED -> PRED 
    = \(X :: PRED) -> 
      \(a :: Ot) -> 
      case a of 
         (O) -> n1code@SET     -- t@SET (n1code@set)
         (S a') -> X a'
         (L ls) -> PIN (\(n :: Nat) -> X (ls n)) 

  PROG (X :: PRED) :: SET
    = PIOT (\( a :: Ot ) -> B' X a `ARR` X a) 

  {- Accessibility of a notation. 
     Quantifies over pred. -}

  Acc (a :: Ot) :: Set
    = (X :: pred) -> 
         el (prog X `arr` X a)

  Acc0 :: Acc zero
    = \(X::pred) -> \(a::Prog X) -> a zero star 

  AccS (a :: Ot) :: Acc a -> Acc (succ a) 
    = \(h :: Acc a) -> 
      \(X :: pred) -> 
      \(pX :: Prog X) -> 
      pX (succ a) (h X pX) 

  AccL (fs :: Seq Ot) :: ((n :: Nat) -> Acc (fs n)) -> Acc (limit fs)
    = \(h :: (n::Nat) -> Acc (fs n)) -> 
      \(X :: pred) -> 
      \(pX :: Prog X) -> 
      pX (limit fs) (\(n::Nat) -> h n X pX) 

  acc_code (a :: Ot) :: SET
    = PI predcode (\(X :: pred) -> 
         t@SET (prog X `arr` X a))

  ACC (a :: Ot) :: Set
    = (X :: PRED)->  
         EL (PROG X `ARR` X a)

  {- That if a predicate is closed under an operation, then 
     it is also closed under all iterates of that operation. -}
  closureLemma (X :: pred) 
               (f :: op Ot) 
               (clf :: el (X `clunder` f))
    :: el (pin (\(n :: Nat) -> X `clunder` OpIt f n))
    = \(n :: Nat) -> 
      \(a :: Ot) -> 
      \(xa :: el (X a)) -> 
      Rec ( \(k :: Nat) -> 
            el (X (OpIt f k a)) )
          xa ( \(n' :: Nat) -> 
               \(h :: el (X (OpIt f n' a))) ->
                  clf (OpIt f n' a) h) n


  {- That the intersection of a sequence of progressive 
     predicates  is itself progressive.  -}
  capnProg (ps :: Seq pred) 
    :: el ((pin (\(n :: Nat) -> prog (ps n))) 
           `arr` prog (capn ps))
    =  \ (psp :: el (pin (\(n :: Nat) -> prog (ps n)) )) ->
       let L :: pred = B (capn ps) 
           body (n :: Nat) 
              :: el (B (capn ps) `subset` ps n) =
                let M :: pred = B (ps n) 
                    step1 :: el (capn ps `subset` ps n) 
                            = capnLemOut ps n 
                    step2 :: el (B (capn ps) `subset` B (ps n)) 
                            = BM (capn ps) (ps n) step1 
                in subsetTrans L M (ps n) step2 (psp n) 
       in capnLemIn ps L body  

{-------------- predicate transformers -----------}

  PT      :: Set          = op pred 
  PT'     :: SET          = predcode `ARR` predcode
  PTid    :: PT           = \(x :: pred) -> x

  {- composition of predicate transformers -}
  PTcomp  :: op2 PT       = \(f :: PT) -> \(g :: PT) -> 
                            \(x :: pred) -> f (g x) 

  {- iteration of predicate transformers. -}
  ItPT    :: PT -> Seq PT = It pred 

  {- pointwise intersection of sequences of PTs. -}
  PTlim   :: Seq PT -> PT
    = \(pts :: Seq PT) -> \(a :: pred) -> 
      capn (\(n :: Nat) -> pts n a)

  {- preservation of progressivity by a PT -}

  PProg (F :: pred -> pred) :: Set
    = (X :: pred) -> 
        Prog X -> Prog (F X) 

  {- same thing reflected as a SET -}
  PPROG(F :: pred -> pred) :: SET
    = PI predcode (\(X :: pred) -> 
         t@SET (prog X `arr` prog (F X)))

  {- Composition preserves preservation of progressivity -}

  PProgComp
      (F :: PT ) (pF :: PProg F)
      (G :: PT ) (pG :: PProg G)
      :: PProg (PTcomp F G)
    = \(X :: pred) -> 
      \(p :: Prog X) -> 
      pF (G X) (pG X p) 

  {- Identity PT preserves progressivity. -}

  PProgId ::  PProg PTid
    = \(X :: pred) -> \(h :: Prog X) -> h
      
  {- Iteration preserves preservation of progressivity. -}

  ItPProg (F :: PT) (pF :: PProg F)
          (n :: Nat)
      :: PProg (ItPT F n) 
    = \(X :: pred) -> \(pX :: Prog X) -> 
      Rec (\(k :: Nat) -> Prog (ItPT F k X)) 
          pX (\(k :: Nat) -> \(h' :: Prog (ItPT F k X)) -> 
          pF (ItPT F k X) h') n

  {- Given a sequence of predicate transformers, 
     if they each  preserve progressivity, 
     then so does their pointwise limit -}
  PProgLim ( pts :: Seq PT) 
           ( pp :: (n :: Nat)-> PProg (pts n) )
    :: PProg (PTlim pts)
    = \(X :: pred) -> 
      \(p :: Prog X) -> 
      capnProg (\(n :: Nat) -> pts n X) 
               (\(n :: Nat) -> pp n X p)

  {- Gentzen's PT -}
  G :: PT 
    = \(X :: pred) -> 
         X `clunder2` (\(a, b :: Ot) -> b `w` a)  

  GentzensLemma :: PProg G 
    = \(X :: pred) ->
      \(p :: Prog X) -> 
      \(x :: Ot) -> 
      \(h :: el (B (G X) x)) -> 
      \(a :: Ot) -> 
      \(xa :: el (X a)) -> 
      let arg ::  el (B X (a `w` x))
            = case x of 
              (O)    -> xa   
              (S a') -> 
               let  f   :: Ot -> Ot 
                         = \(x :: Ot) -> x `w` a' 
                    itf :: Nat -> Ot 
                         = \(k :: Nat)-> It Ot f k a 
               in Rec (\(n :: Nat) -> el (X (itf n)))
                       xa (\(n :: Nat) -> h (itf n))
              (L ls) -> (\(n :: Nat) -> h n a xa)   
      in p (a `w` x) arg

  LensLemmaG (a :: Ot) (acca :: Acc a) 
             (b :: Ot) (accb :: Acc b)
    :: Acc (w a b)
    = \(X::pred) -> 
      \(pX::el (prog X)) -> 
      accb (G X) (GentzensLemma X pX) a (acca X pX)

  {- A protolens is a predicate transformer that 
     preserves progressivity -}

  ProtoLens :: Set
    = Si PT PProg 

  {- Coded as a large set -}
  PROTOLENS :: SET    = si@SET PT' PPROG

  ProtoLensId :: ProtoLens 
    = struct 
        fst = PTid
        snd = PProgId 

  ProtoLensComp :: op2 ProtoLens 
    = \(f :: ProtoLens) -> 
      \(g :: ProtoLens) -> 
        struct 
          fst = PTcomp f.fst g.fst
          snd = PProgComp f.fst f.snd g.fst g.snd

  {- Finite iteration of proto-lenses -}
  ProtoLensIt :: ProtoLens -> Seq ProtoLens
    = \(pl :: ProtoLens) -> 
      \(n :: Nat) -> 
      It ProtoLens (ProtoLensComp pl) n pl

  {- The notion of Lens -}
  Lens  (f :: op Ot) :: Set
    = Si ProtoLens (\(pl :: ProtoLens) -> 
         (X :: pred) -> Prog X -> 
         el ((pl.fst X) `subset` (X `sub` f) ))

  {- Coded as a large set -} 
  LENS (f :: op Ot) :: SET
    = si@SET PROTOLENS (\(pl :: ProtoLens) -> 
          PI predcode (\(X :: pred) -> 
             t@SET (prog X `arr` (pl.fst X `subset` (X `sub` f))) ))

  {- The accessible notations are closed under any operation that
     possesses a lens. -}

  LensLemmaV (f :: op Ot) 
            (lf :: Lens f) 
            (a :: Ot) 
    :: Acc a -> Acc (f a)
    = \(h :: Acc a) -> 
      \(X :: pred) -> 
      \(pX :: Prog X) -> 
      lf.snd X pX a (h (lf.fst.fst X) (lf.fst.snd X pX))

  {- The identity function possesses a lens -}

  LensId :: Lens (\(x :: Ot) -> x)
    = struct 
        fst = ProtoLensId
        snd = \(X :: pred) -> 
              \(pX :: Prog X) -> 
              \(a :: Ot) -> 
              \(xa :: el (X a)) -> xa

  {- Closure of lenses under composition. -}

  LensComp (f :: op Ot) (lf :: Lens f) 
           (g :: op Ot) (lg :: Lens g) 
           :: Lens (\(a :: Ot) -> f (g a))
    = struct 
        fst = ProtoLensComp lg.fst lf.fst
        snd = \(X :: pred) -> \(pX :: Prog X) -> 
              \(a :: Ot) -> 
              \(a' :: el (fst.fst X a)) -> 
              lf.snd X pX 
                     (g a) (lg.snd (lf.fst.fst X) 
                                   (lf.fst.snd X pX) a a')

  GentzensProtoLens :: ProtoLens
    = struct 
        fst = G
        snd = GentzensLemma

  GentzenLens :: Lens wexp 
    = struct 
        fst = GentzensProtoLens
        snd = \(X :: pred) -> 
              \(p :: Prog X) -> 
              \(a :: Ot) -> 
              \(h :: el (G X a)) -> 
              h zero (p zero star)  

  {- A closure lens for an operator f is a protolens (F,..), 
     such that F X subset X on progressive 
     predicates X (i.e. a lens for the identity 
     function), and such that if X is a progressive 
     predicate, then F X is closed under f.  -}
     
  CLens (f :: op Ot) :: Set
    = Si  ProtoLens (\(pl :: ProtoLens) ->
        and ( (X :: pred) -> 
              el (prog X `arr` (pl.fst X `subset` X )))
            ( (X :: pred) -> 
              el (prog X `arr` (pl.fst X `clunder` f))))

  {- We can make a closure lens from a lens.
     The idea is fairly simple, though in a way
     the key to the whole construction. 
     Just take the limit-by-intersection of the finite
     iterates of the predicate transformer.
  -}
  MkClens ( f :: op Ot ) :: Lens f -> CLens f 
    = \(l :: Lens f) -> 
      let 
        pt  :: PT = l.fst.fst 
        pp  :: PProg pt = l.fst.snd 
        dr  :: (X :: pred) -> Prog X -> 
                  el (pt X `subset` sub X f) 
            = l.snd 
        pt' :: PT 
            = PTlim (ItPT pt)  
        pp' :: PProg pt'  
            = PProgLim (ItPT pt) (ItPProg pt pp)  
        cl1 :: (X :: pred) -> 
               (p :: Prog X) -> 
               el (pt' X `subset` X)  
            = \(X :: pred) -> 
              \(_ :: Prog X) -> 
              \(a :: Ot) -> 
              \(x :: el (pt' X a)) -> 
              x Naturals.zero  
        cl2 :: (X :: pred) -> 
               (_ :: Prog X) -> 
               el (pt' X `clunder` f)  
            = \(X :: pred) -> 
              \(pX :: Prog X) -> 
              \(a :: Ot) -> 
              \(x :: el (pt' X a)) ->
              \(n :: Nat) -> 
              dr (ItPT pt n X) 
                 (ItPProg pt pp n X pX) 
                 a 
                 (x (Naturals.succ n)) 
      in struct 
           fst = struct 
                  fst = pt'
                  snd = pp'
           snd = struct 
                  fst = cl1
                  snd = cl2

  {- Given a closure lens for an operator, 
     we can get another one for the omega-iteration 
     of that operator. This is where
     the word "closure" comes from. -}

  ItClens ( f :: op Ot ) 
    :: CLens f -> CLens (OpItw f)
    = \(cl  :: CLens f) -> 
      let   pl :: ProtoLens 
               = cl.fst 
            pt :: PT 
               = pl.fst 
            pp :: PProg pt 
               = pl.snd 
            pf :: (X :: pred) -> Prog X -> 
                  el (pt X `subset` X) 
                 = cl.snd.fst 
            cls :: (X :: pred) -> (p :: Prog X) -> 
                    el (clunder (pt X) f) 
                 = cl.snd.snd 
            cls' :: (X :: pred) -> (p :: Prog X) -> 
                    el (pt X `clunder` OpItw f) 
             = \(X :: pred) -> 
               \(pX :: Prog X) -> 
               \(a :: Ot) -> 
               \(x :: el (pt X a)) -> 
               pp X pX (OpItw f a) (\(n :: Nat) ->  
               closureLemma (pt X) f (cls X pX) n a x)
      in struct 
           fst = pl
           snd = struct 
                   fst = pf
                   snd = cls'

  {- Given a sequence of lenses for a sequence of functions,
     we can form a lens for their pointwise sup. -}

  {- Really uses only that progressive implies closed -}
  SupLens (fs :: Seq (op Ot)) 
          (ls :: (n :: Nat) -> Lens (fs n))
          :: Lens (OpLim fs)
    = let
        pts (n :: Nat) :: PT 
                = (ls n).fst.fst 
        pps (n :: Nat) :: PProg (pts n) 
                = (ls n).fst.snd 
        drs (n :: Nat) 
               :: (X :: pred) -> 
                  Prog X -> 
                  el ( (pts n X) `subset` (X `sub` fs n))  
               = (ls n).snd 
        pt :: PT = PTlim pts  
        pp :: PProg pt = PProgLim pts pps  
        dr (X :: pred) (pX :: Prog X) 
               ::  el (pt X `subset` (X `sub` (OpLim fs)))
               = \(a :: Ot) -> 
                 \(xa :: el (pt X a)) -> 
                 pX (OpLim fs a) 
                    (\(n :: Nat) -> 
                          drs n X pX a (xa n)) 
      in struct 
           fst = struct 
                   fst = pt
                   snd = pp 
           snd = dr 

  {- If we have a closure lens for f, then 
     we can get a lens for Nabla f. 
     It is maybe unhygienic that there is a case 
     distinction here. 
  -}

  NablaLens (f :: op Ot) 
            (cl :: CLens f ) 
    :: Lens (Nabla f) 
    = let
        pt  :: PT            = cl.fst.fst        
        pp  :: PProg pt      = cl.fst.snd  
        pf  :: (X :: pred) -> Prog X -> 
                 el (pt X `subset` X) 
            = cl.snd.fst 
        cls :: (X :: pred) -> (p :: Prog X) -> 
                   el (pt X `clunder`f) 
            = cl.snd.snd               
        pt' :: PT 
            = \(X :: pred) -> pt X `sub` Nabla f 
        pp' :: PProg pt'
            = \(X :: pred) -> 
              \(pX :: Prog X) -> 
              \(a :: Ot) -> 
              \(h ::  el (B (pt' X) a)) -> 
              case a of 
                (O)    -> cls X pX a (pp X pX a star)
                (S a') -> cls X pX (succ (Nabla f a')) 
                             (pp X pX (succ (Nabla f a')) h) 
                (L ls) -> pp X pX (Nabla f a) h      
        dr' (X :: pred) (pX :: Prog X)
            :: el ((pt' X) `subset` (X `sub` (Nabla f)))
            = \(a :: Ot) -> pf X pX (Nabla f a)    
      in struct 
           fst = struct 
                  fst = pt'
                  snd = pp' 
           snd = dr'

  {- The following predicate is pivotal. -}
  LensPredicate (a :: Ord) :: SET
    = LENS (v a)

  SuccLens (f :: op Ot) (lf :: Lens f)
    :: Lens (deriv f)
    = NablaLens (OpItw f) 
                (ItClens f (MkClens f lf)) 

  LimLens (fs :: Seq (op Ot)) 
          (lfs :: (n :: Nat) -> Lens (fs n)) 
    :: Lens (derivl fs)
    = let  f :: op Ot = OpLim fs 
      in   NablaLens f (MkClens f (SupLens fs lfs))

  ZeroLens :: Lens (deriv wexp) 
    = SuccLens wexp GentzenLens

--------------------------------------------------------
{- We are now back outside the "small" package. The file
  concludes with a proof of the accessibility of
  Gamma_0 -}

{- Next universe operator. -}

NextU (FS :: Fam Set) :: Fam Set
   = (small FS).Next

{- Accessibility relative to a family of sets -}
acc (FS :: Fam Set) :: Ord -> Set
   = (small FS).Acc

ACC (FS :: Fam Set) :: Ord -> Set
   = acc (NextU FS) 

{- The set of lenses relative to a family of sets -}
Lens (FS :: Fam Set)(f :: Ord -> Ord) :: Set
   = (small FS).Lens f

PRED (FS :: Fam Set)
   :: Set
   = (small (NextU FS)).pred

{- The predicate wrt FS that Lens (v a) -}
lenspred (FS :: Fam Set) 
   :: PRED FS 
   = (small FS).LensPredicate 

PROG (FS :: Fam Set)
   :: Pow (PRED FS) 
   = (small (NextU FS)).Prog 

{- That the above predicate is progressive -}
lenspredprog (FS :: Fam Set) 
   :: PROG FS (lenspred FS) 
   = \(a::Ord) -> 
     case a of 
        (O) -> \(_::N1) -> 
                  (small FS).ZeroLens
        (S a') -> (small FS).SuccLens 
                       (v a')
        (L ls) -> (small FS).LimLens 
                       (\(n::Nat) -> v (ls n))

{- The key lemma which shows how for each 
   layer of the veblen hierarchy, you can 
   use another universe -}
 
LemmaV (FS :: Fam Set) 
      (a :: Ord)
      (acca :: ACC FS a)
   :: (b :: Ord) -> acc FS b -> acc FS (v a b) 
   = let vl :: Lens FS (v a) 
            = acca (lenspred FS) (lenspredprog FS) 
     in (small FS).LensLemmaV (v a) vl

{- Just for completeness, we pull out 
   of the package above the corresponding 
   lemma for the function w. -}

LemmaG (FS :: Fam Set) 
      (a :: Ord)
      (acca :: acc FS a)
   :: (b :: Ord) -> acc FS b -> acc FS (w a b) 
   = (small FS).LensLemmaG a acca

{- RECURSIVE
   The main theorem.  
   To express the recursion by use of NatRec, we 
   would need a superuniverse closed under NextU -}

Theorem (FS :: Fam Set) (n :: Nat) 
    :: acc FS (pd Gamma0 n) 
    =  case n of 
         (Z) ->  (small FS).Acc0 
         (S p) -> LemmaV FS 
                    (pd Gamma0 p) (Theorem (NextU FS) p) 
                     zero         (small FS).Acc0

Corollary (FS :: Fam Set) 
    :: acc FS Gamma0
    = (small FS).AccL (pd Gamma0) (Theorem FS) 
