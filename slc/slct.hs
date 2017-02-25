{-

SSLC : Simplified Symbolic Lambda Calculus

MAIN IDEAS

SSLC is a formal system for proving equality of terms called symbolic lambda-terms derived from SLC. The following simplifications are introduced :
- instead of a potential infinity of symbols, there is only one symbol (SMB)
- like in SLC, De Bruijn index notation is used, but the variable (DBV n) is replaced by (DBS (DBS ... (DBS DB0) ... )) with DBS repeated n times
- there is only one axiom
These simplifications does not introduce restrictions : several symbols may be represented by different terms applied to the unique symbol, and several axioms a1 = b1, a2 = b2, ... , an = bn may be represented by a unique axiom, for example  <a1, a2, ..., an> = <b1, b2, ... , bn>

A SSLC term or proof may be 
 - (SMB) the unique symbol
 - (DB0) the initial variable 
 - (DBS x) the variable following x
 - (DBL x) abstraction, where x is a SSLC term
 - (APL x y) application of SSLC term x to SSLC term y
 - (LTR x y) left transitivity - symmetry with reduction applied to SSLC terms x and y
             representing the rule a = b, c = d, a -> e, c -> e, b -> f, d -> g => f = g
 - (AXM) the unique axiom

Reduction of a term is defined by iterating a reduction step which consists of substituting (AP (DBL x) y) by the result of the substitution in x of variables whose index equals to the nesting level in DBL terms by y, according to De Bruijn index notation.

Like in SLC, SSLC terms represent both extended (with (SMB)) lambda-terms and proofs in theories. A theory t is represented by a unique axiom u = v.
To any SSLC term and any theory are associated two SSLC terms called left and right. A SSLC term is associated to a proof in theory t of the equality of its left and its right : x proves left(t,x) = right(t,x). Symbolic lambda-terms are particular SSLC terms which represent both a symbolic lambda-term and the proof that this symbolic lambda-term equals itself. Left and right of a lambda-term is itself.

Any SSLC term proves that its left equals its right. In a theory t with axiom u = v : 

 - (SMB) proves (SMB) = (SMB)
 - (DB0) proves (DB0) = (DB0)
 - (DBS x) proves (DBS a) = (DBS b) if x proves a = b
 - (DBL x) proves (DBL a) = (DBL b) if x proves a = b
 - (APL x y) proves (APL a c) = (APL b d) if x proves a = b and y proves c = d
   in other terms, if a = b and c = d then (APL a c) = (APL b d)
 - (LTR x y) proves f = g if x proves a = b, y proves c = d, a reduces to e, c reduces to e, b reduces to f and d reduces to g, otherwise it proves (LTR x y) = (LTR x y)
 - (AXM) proves u = v.


Example of running with hugs :

$ (echo ':load Slc_tirp'; echo 'test'; echo 'run "gdparent.slc"'; echo 'run "prop.slc"') | hugs -h10000k

-}

module Slc_tirp where

 import Data.List
 import Data.Char


 data Proof = Proof0 Rule0 | Proof1 Rule1 Proof | Proof2 Rule2 Proof Proof
  deriving (Eq)

 data Rule0 = AXM | DB0 | SMB String
  deriving (Eq)

 data Rule1 = DBS | DBL
  deriving (Eq)

 data Rule2 = APL | LTR | EQU
  deriving (Eq)

 instance Show Rule0 where
  show AXM = "AXM"
  -- show DB0 = "DB0"
  show DB0 = "@"
  show (SMB s) = s

 instance Show Rule1 where
  -- show DBS = "+"
  show DBS = "'"
  show DBL = "\\"
 
 instance Show Rule2 where
  show EQU = "="
  show APL = "-"
  show LTR = "LTR"

 spaces = "  "

 showlevel :: Int -> Int -> Proof -> String
 showlevel i l (Proof0 (SMB s)) = concat (replicate (i*l) spaces) ++ s 
 showlevel i l (Proof0 r) = concat (replicate (i*l) spaces) ++ show r
 showlevel i l (Proof1 r x) = concat (replicate (i*l) spaces) ++ show r ++ " " ++ showlevel 0 (l+1) x 
 showlevel i l (Proof2 r x y) = concat (replicate (i*l) spaces) ++ show r ++ " " ++ showlevel 0 (l+1) x ++ "\n" ++ showlevel 1 (l+1) y 

 showapl (Proof2 APL x y) (Proof2 APL z t) = showapl x y ++ " : " ++ showapl z t
 showapl (Proof2 APL x y) z = showapl x y ++ " " ++ show z
 showapl x (Proof2 APL y z) = show x ++ " : " ++ showapl y z
 showapl x y = show x ++ " " ++ show y

 showproof (Proof0 (SMB s)) = s
 showproof (Proof2 APL x y) = "(" ++ showapl x y ++ ")"
 showproof (Proof0 r) = show r
 showproof (Proof1 r x) = show r ++ showproof x
 showproof (Proof2 r x y) = show r ++ " " ++ showproof x ++ " " ++ showproof y

 instance Show Proof where
  -- show x = showlevel 1 0 x
  show x = showproof x

 axm = Proof0 AXM
 db0 = Proof0 DB0
 smb s = Proof0 (SMB s)
 dbs x = Proof1 DBS x
 dbl x = Proof1 DBL x
 apl x y = Proof2 APL x y
 ltr x y = Proof2 LTR x y
 equ x y = Proof2 EQU x y

 data Side = LeftSide | RightSide
  deriving (Eq, Show)

 intfrom n = n : (intfrom (n+1))

 append [] l = l
 append (x : l1) l2 = x : append l1 l2

 maplfa [] f = []
 maplfa (x : l) f = (f x) ++ (maplfa l f)

 merge [] l2 = l2
 merge l1 [] = l1
 merge (x1 : l1) (x2 : l2) = x1 : x2 : merge l1 l2 

 maplfm [] f = []
 maplfm (x : l) f = merge (f x) (maplfm l f)

 firsts n l = if n == 0 then [] else (head l) : firsts (n-1) (tail l)

 showlist [] = ""
 showlist (x : l) = show x ++ "\n" ++ showlist l

 proofs = axm : db0 : smb "SMB" :
  (maplfa proofs $ \x -> 
    dbs x : 
    dbl x : 
    (maplfa proofs $ \y ->
      apl x y :
      ltr x y :
      [] ) )
 
 suc_digits [] = [1]
 suc_digits (0 : l) = 1 : l
 suc_digits (1 : l) = 0 : suc_digits l
 
 -- digits :: Nat -> [Nat]
 digits :: Int -> [Int]
 digits 0 = [0]
 digits (n+1) = suc_digits (digits n)

 nat_of_digits :: [Int] -> Int 
 nat_of_digits [] = 0
 nat_of_digits (b : l) = b + 2 * nat_of_digits l

 even_items [] = []
 even_items (x : []) = [x]
 even_items (x : _ : l) = x : even_items l

 first = nat_of_digits . even_items . digits 
 second = nat_of_digits . even_items . tail . digits
 
 axioms = [
  slc "^x ^y ^z =  - (parent x y) - (parent y z) (gdparent x z) \\@",
  slc "= (parent allan brenda) \\@",
  slc "= (parent brenda charles) \\@"]

 naxm = length axioms

 -- nthproof 0 = axm
 nthproof n = if n < naxm then axioms !! n else nthproof1 (n - naxm)

 nthproof1 0 = db0
 nthproof1 1 = smb "SMB"
 nthproof1 (n+2) = let p = div n 4 in case mod n 4 of
  0 -> dbs $ nthproof p
  1 -> dbl $ nthproof p
  2 -> apl (nthproof $ first p) (nthproof $ second p)
  3 -> ltr (nthproof $ first p) (nthproof $ second p)

 show1 x = show x ++ " proves " ++ show (left x) ++ " = " ++ show (right x)

 show_proofs n 0 = ""
 show_proofs n (p+1) = show1 (nthproof n) ++ "\n" ++ show_proofs (n+1) p

 display_proofs n = putStr (show_proofs 0 n)

 prove a b = prove1 0 a b

 prove1 n a b = let x = nthproof n in if (((left x) == a) && ((right x) == b)) then x else prove1 (n+1) a b

 testprove = prove (slc "gdparent allan brenda") (dbl db0)


{-
 print_proof n = do
  putStrLn $ show $ nthproof n 

 print_proofs n p = do
  if n > p then return else do
   print_proof n
   print_proofs (n+1) p
   return
-}


 split1 b d w [] = [w]
 split1 b d w (x : s) = 
  if elem x b 
  then (if w == [] 
        then split1 b d [] s 
        else w : split1 b d [] s) 
  else if elem x d 
  then (if w == [] then [x] : split1 b d [] s else w : [x] : split1 b d [] s)
  else split1 b d (w ++ [x]) s

 split n d s = split1 n d [] s


 slc1 ("AXM" : s) = (axm, s)
 slc1 ("DB0" : s) = (db0, s)
 slc1 ("$"   : s) = (db0, s)
 slc1 ("@"   : s) = (db0, s)
 slc1 ("DBS" : s) = let (x, t) = slc1 s in (dbs x, t)
 slc1 ("+"   : s) = let (x, t) = slc1 s in (dbs x, t)
 slc1 ("'"   : s) = let (x, t) = slc1 s in (dbs x, t)
 slc1 ("DBL" : s) = let (x, t) = slc1 s in (dbl x, t)
 slc1 ("\\"  : s) = let (x, t) = slc1 s in (dbl x, t)
 slc1 ("APL" : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (apl x y, u)
 slc1 ("-"   : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (apl x y, u)
 slc1 ("LTR" : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (ltr x y, u)
 slc1 ("&"   : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (ltr x y, u)
 slc1 ("EQU" : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (equ x y, u)
 slc1 ("="   : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (equ x y, u)
 slc1 ("LET" : v : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (apl (lambda v y) x, u)
 -- slc1 (":"   : v : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (apl (lambda v y) x, u)
 slc1 ("LBD" : v : s) = let (x, t) = slc1 s in (lambda v x, t)
 slc1 ("^"   : v : s) = let (x, t) = slc1 s in (lambda v x, t)
 slc1 ("("   : s) = slc2 s (dbl db0) False 
 slc1 (":"   : s) = slc2 s (dbl db0) True
 slc1 (w : s) = (smb w, s)

 slc2 (")" : s) x False = (x, s)
 slc2 (")" : s) x True = (x, ")" : s)
 slc2 s (Proof1 DBL (Proof0 DB0)) c = let (y, t) = slc1 s in slc2 t y c
 slc2 s x c = let (y, t) = slc1 s in slc2 t (apl x y) c

{-
 slc1 :: [[Char]] -> [Proof] -> (Proof, [[Char]], [Proof])
 slc1 ("AXM" : s) l = (axm, s, l)
 slc1 ("DB0" : s) l = (db0, s, l)
 slc1 ("$"   : s) l = (db0, s, l)
 slc1 ("@"   : s) l = (db0, s, l)
 slc1 ("DBS" : s) l = let (x, t, m) = slc1 s l in (dbs x, t, m)
 slc1 ("+"   : s) l = let (x, t, m) = slc1 s l in (dbs x, t, m)
 slc1 ("'"   : s) l = let (x, t, m) = slc1 s l in (dbs x, t, m)
 slc1 ("DBL" : s) l = let (x, t, m) = slc1 s l in (dbl x, t, m)
 slc1 ("\\"  : s) l = let (x, t, m) = slc1 s l in (dbl x, t, m)
 slc1 ("APL" : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl x y, u, n)
 slc1 ("-"   : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl x y, u, n)
 slc1 ("LTR" : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (ltr x y, u, n)
 slc1 ("&"   : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (ltr x y, u, n)
 slc1 ("EQU" : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (equ x y, u, n)
 slc1 ("="   : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (equ x y, u, n)
 slc1 ("LET" : v : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl (lambda v y) x, u, n)
 -- slc1 (":"   : v : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl (lambda v y) x, u, n)
 slc1 ("LBD" : v : s) l = let (x, t, m) = slc1 s l in (lambda v x, t, m)
 slc1 ("^"   : v : s) l = let (x, t, m) = slc1 s l in (lambda v x, t, m)
 slc1 ("("   : s) l = slc1 s ((dbl db0) : l)
 slc1 (")"   : s) (x : l) = (x, s, l)
 slc1 (w : s) l = (smb w, s, l)
-}

{-
 slc1 :: [[Char]] -> [Proof] -> Bool -> (Proof, [[Char]], [Proof])
 slc1 ("AXM" : s) l c = (axm, s, l)
 slc1 ("DB0" : s) l c = (db0, s, l)
 slc1 ("$"   : s) l c = (db0, s, l)
 slc1 ("@"   : s) l c = (db0, s, l)
 slc1 ("DBS" : s) l c = let (x, t, m) = slc1 s l c in (dbs x, t, m)
 slc1 ("+"   : s) l c = let (x, t, m) = slc1 s l c in (dbs x, t, m)
 slc1 ("'"   : s) l c = let (x, t, m) = slc1 s l c in (dbs x, t, m)
 slc1 ("DBL" : s) l c = let (x, t, m) = slc1 s l c in (dbl x, t, m)
 slc1 ("\\"  : s) l c = let (x, t, m) = slc1 s l c in (dbl x, t, m)
 slc1 ("APL" : s) l c = let (x, t, m) = slc1 s l c in let (y, u, n) = slc1 t m c in (apl x y, u, n)
 slc1 ("-"   : s) l c = let (x, t, m) = slc1 s l c in let (y, u, n) = slc1 t m c in (apl x y, u, n)
 slc1 ("LTR" : s) l c = let (x, t, m) = slc1 s l c in let (y, u, n) = slc1 t m c in (ltr x y, u, n)
 slc1 ("&"   : s) l c = let (x, t, m) = slc1 s l c in let (y, u, n) = slc1 t m c in (ltr x y, u, n)
 slc1 ("EQU" : s) l c = let (x, t, m) = slc1 s l c in let (y, u, n) = slc1 t m c in (equ x y, u, n)
 slc1 ("="   : s) l c = let (x, t, m) = slc1 s l c in let (y, u, n) = slc1 t m c in (equ x y, u, n)
 slc1 ("LET" : v : s) l c = let (x, t, m) = slc1 s l c in let (y, u, n) = slc1 t m c in (apl (lambda v y) x, u, n)
 -- slc1 (":"   : v : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl (lambda v y) x, u, n)
 slc1 ("LBD" : v : s) l c = let (x, t, m) = slc1 s l c in (lambda v x, t, m)
 slc1 ("^"   : v : s) l c = let (x, t, m) = slc1 s l c in (lambda v x, t, m)
 slc1 ("("   : s) l c = slc1 s ((dbl db0) : l) c
 slc1 (")"   : s) (x : l) c = (x, s, l)
 slc1 (w : s) l c = (smb w, s, l)
-}

{-
 -- slc1 :: [[Char]] -> [Proof] -> (Proof, [[Char]], [Proof])
 slc1 ("AXM" : s) l = (axm, s, l)
 slc1 ("DB0" : s) l = (db0, s, l)
 slc1 ("$"   : s) l = (db0, s, l)
 slc1 ("@"   : s) l = (db0, s, l)
 slc1 ("DBS" : s) l = let (x, t, m) = slc1 s l in (dbs x, t, m)
 slc1 ("+"   : s) l = let (x, t, m) = slc1 s l in (dbs x, t, m)
 slc1 ("'"   : s) l = let (x, t, m) = slc1 s l in (dbs x, t, m)
 slc1 ("DBL" : s) l = let (x, t, m) = slc1 s l in (dbl x, t, m)
 slc1 ("\\"  : s) l = let (x, t, m) = slc1 s l in (dbl x, t, m)
 slc1 ("APL" : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl x y, u, n)
 slc1 ("-"   : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl x y, u, n)
 slc1 ("LTR" : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (ltr x y, u, n)
 slc1 ("&"   : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (ltr x y, u, n)
 slc1 ("EQU" : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (equ x y, u, n)
 slc1 ("="   : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (equ x y, u, n)
 slc1 ("LET" : v : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl (lambda v y) x, u, n)
 -- slc1 (":"   : v : s) l = let (x, t, m) = slc1 s l in let (y, u, n) = slc1 t m in (apl (lambda v y) x, u, n)
 slc1 ("LBD" : v : s) l = let (x, t, m) = slc1 s l in (lambda v x, t, m)
 slc1 ("^"   : v : s) l = let (x, t, m) = slc1 s l in (lambda v x, t, m)
 slc1 ("("   : s) l = slc1 s ((dbl db0, False) : l)
 slc1 (":"   : s) l = slc1 s ((dbl db0, True ) : l)
 slc1 (")"   : s) ((x,False) : l) = (x, s, l)
 slc1 (")"   : s) ((x,True ) : l) = (x, ")" : s, l)
 slc1 (w : s) l = (smb w, s, l)

 -- slc2 s l = let (x, t, m) = slc1 s l in if m == [] then (x, t) else if head m == dbl db0 then slc2 t (x : tail m) else slc2 t ((apl (head m) x) : tail m)
 slc2 s l = let (x, t, m) = slc1 s l in case m of
  [] -> (x, t)
  (Proof1 DBL (Proof0 DB0), c) : n -> slc2 t ((x,c) : n)
  (y, c) : n -> slc2 t ((apl y x, c) : n) 

-}

{-
 slc2 ("(" : s, l) = slc2 (s, (dbl db0) :: l)
 slc2 (")" : s, x :l) = (x, s)
 slc2 (s, []) = slc1 (s)
-}

 -- slc s = let (x, t) = slc1 (split " " s) in if t == [] then Just x else Nothing
 slc s = let (x, t) = slc1 (split " \t\n" "@$'\\^()" ("( " ++ s ++ " )")) in if t == [] || head t == "" then x else smb ("Error : Unexpected '" ++ concat (map (\x -> x ++ " ") t) ++ "'")
 -- slc s = let (x, t) = slc2 (split " \t\n" s) [] in if t == [] || head t == "" then x else smb ("Error : Unexpected '" ++ concat (map (\x -> x ++ " ") t) ++ "'")

 -- x contains y ?
 cont :: Proof -> Proof -> Bool
 cont1 :: Proof -> Proof -> Bool
 cont x y = if x == y then True else cont1 x y
 cont1 (Proof0 r) _ = False
 cont1 (Proof1 r x) y = cont x y
 cont1 (Proof2 r x y) z = (cont x z) || (cont y z) 

 shift :: Proof -> Proof -> Proof
 shift1 :: Proof -> Proof -> Proof
 shift u x = if u == x then Proof1 DBS x else shift1 u x
 shift1 u (Proof1 DBL x) = Proof1 DBL (shift (Proof1 DBS u) x)
 shift1 _ (Proof0 r) = Proof0 r
 shift1 u (Proof1 r x) = Proof1 r (shift u x)
 shift1 u (Proof2 r x y) = Proof2 r (shift u x) (shift u y)

 subst :: Proof -> Proof -> Proof -> Proof
 subst1 :: Proof -> Proof -> Proof -> Proof
 subst u a b = if u == a then b else (if Proof1 DBS u == a then u else subst1 u a b)
 -- subst1 u (Proof1 DBL x) b = Proof1 DBL (subst (Proof1 DBS u) x (shift (Proof0 DB0) b))
 subst1 u (Proof1 DBL x) b = Proof1 DBL (subst (Proof1 DBS u) x (shift u b))
 -- subst1 u (Proof1 DBL x) b = if u == Proof0 DB0 then Proof1 DBL (subst (Proof1 DBS u) x (shift (Proof0 DB0) b)) else Proof1 DBL (subst u x b)
 subst1 _ (Proof0 r) _ = Proof0 r
 subst1 u (Proof1 r x) b = Proof1 r (subst u x b)
 subst1 u (Proof2 r x y) b = Proof2 r (subst u x b) (subst u y b)

 -- One step of reduction 
 red1 :: Proof -> Proof
 red1 (Proof2 APL (Proof1 DBL x) y) = subst (Proof0 DB0) x y
 red1 (Proof0 r) = Proof0 r
 red1 (Proof1 r x) = Proof1 r (red1 x)
 red1 (Proof2 r x y) =
  let x1 = red1 x in
   if x == x1 then Proof2 r x (red1 y) else Proof2 r x1 y

 red2 :: [Proof] -> [Proof]
 red2 [] = []
 red2 (x : l) = (red1 x) : (x : l)

 red3 :: [Proof] -> [Proof]
 red3 [] = []
 -- red3 (x : l) = if elem x l then (x : l) else red3 (red2 (x : l))
 red3 (x : l) = case find (\y -> cont x y) l of
	Nothing -> red3 (red2 (x : l))
	Just _ -> x : l

 -- reduction to normal form
 reduce :: Proof -> Proof
 reduce x = case red3 (x : []) of
		[] -> x
		y : m -> y
 -- reduce x = if red1 x == x then x else reduce (red1 x)

 r = reduce

 -- n steps of reduction
 rered1 :: Int -> Proof -> Proof
 rered1 n x = if (n == 0) then x else rered1 (n - 1) (red1 x)

 rered1xn x n = rered1 n x

 -- With axiom u = v, proof p proves side leftside u v p = side rightside u v p
 side :: Side -> Proof -> Proof -> Proof -> Proof
 -- AXM |- u = v
 side LeftSide u v (Proof0 AXM) = u
 side RightSide u v (Proof0 AXM) = v
 -- EQU : a, b |- a = b
 side LeftSide _ _ (Proof2 EQU x y) = x
 side RightSide _ _ (Proof2 EQU x y) = y
 -- LTR : a = b, c = d |- if reduce(a) == reduce(c) then reduce(b) = reduce(d)  
 side s u v (Proof2 LTR x y) =
	if reduce (side LeftSide u v x) == reduce (side LeftSide u v y) 
	then reduce (side RightSide u v (if s == LeftSide then x else y)) 
    else Proof2 LTR x y
 side _ _ _ (Proof0 r) = Proof0 r
 side s u v (Proof1 r x) = Proof1 r (side s u v x)
 side s u v (Proof2 r x y) = Proof2 r (side s u v x) (side s u v y)


 var :: String -> Proof
 var x = Proof0 (SMB x)

 -- p contains symbol s ?
 contSmb :: Proof -> String -> Bool
 contSmb (Proof0 (SMB s1)) s2 = s1 == s2
 contSmb (Proof0 r) _ = False
 contSmb (Proof1 r x) s = contSmb x s
 contSmb (Proof2 r x y) s = (contSmb x s) || (contSmb y s)
 
 abstr :: Proof -> String -> Proof -> Proof
 abstr1 :: Proof -> String -> Proof -> Proof
 abstr d v x = if (contSmb x v) then (abstr1 d v x) else x
 abstr1 d v (Proof0 (SMB s)) = if v == s then d else (Proof0 (SMB s))
 abstr1 d v (Proof1 DBL x) = Proof1 DBL (abstr (Proof1 DBS d) v x)
 abstr1 _ _ (Proof0 r) = Proof0 r
 abstr1 d v (Proof1 r x) = Proof1 r (abstr d v x)
 abstr1 d v (Proof2 r x y) = Proof2 r (abstr d v x) (abstr d v y)

 lambda :: String -> Proof -> Proof
 -- lambda v x = Proof1 DBL (abstr (Proof0 DB0) v x)
 lambda v x = dbl (abstr db0 v x)
 -- lambda v x = dbl (abstr dbv v x)

 apl2 :: Proof -> Proof -> Proof -> Proof
 apl2 f x1 x2 = apl (apl f x1) x2

 apl3 :: Proof -> Proof -> Proof -> Proof -> Proof
 apl3 f x1 x2 x3 = apl (apl (apl f x1) x2) x3

 apl4 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl4 f x1 x2 x3 x4 = apl (apl (apl (apl f x1) x2) x3) x4

 apl5 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl5 f x1 x2 x3 x4 x5 = apl (apl (apl (apl (apl f x1) x2) x3) x4) x5

 apl6 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl6 f x1 x2 x3 x4 x5 x6 = apl (apl (apl (apl (apl (apl f x1) x2) x3) x4) x5) x6

 apl7 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl7 f x1 x2 x3 x4 x5 x6 x7 = apl (apl (apl (apl (apl (apl (apl f x1) x2) x3) x4) x5) x6) x7

 apl8 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl8 f x1 x2 x3 x4 x5 x6 x7 x8  = apl (apl (apl (apl (apl (apl (apl (apl f x1) x2) x3) x4) x5) x6) x7) x8


 axl = smb "SMB"
 axr = apl (smb "SMB") (smb "SMB")

 left = side LeftSide axl axr
 right = side RightSide axl axr


 proves x = do
  -- putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")
  putStr ("\nThe proof\n" ++ show x ++ "\nproves\n" ++ show (left x) ++ "\nequals\n" ++ show (right x) ++ "\n")

 reducesTo x = do
  putStr ("\n  " ++ show x ++ "\nreduces to\n  " ++ show (reduce x) ++ "\n")

{-
 pr1 x y = do
  putStr ("\nThe proof\n" ++ show x ++ "\nreduces to\n" ++ show y ++ "\nwhich proves\n" ++ show (left y) ++ "\nequals\n" ++ show (right y) ++ "\n")
-}

 pr1 x y = do
  pr2 x y (left y) (right y)

 pr2 x y l r = do
  putStr ("\nThe proof\n" ++
   show x ++
   "\nreduces to\n" ++
   show y ++
   "\nwhich proves\n" ++
   show l ++
   "\nequals\n" ++
   show r ++
   "\nwhich reduces to\n" ++
   show (reduce l) ++
   "\nequals\n" ++
   show (reduce r) ++
   "\n")

 pr x = do
  pr1 x (reduce x)

 run filename = do
  -- readFile filename >>= \s -> proves $ reduce $ slc s
  readFile filename >>= \s -> pr $ slc s


 ident = dbl db0
 auto = dbl (apl db0 db0)
 comp f g = dbl (apl f (apl g db0))
 fix f = apl auto (comp f auto)
 ias = fix (dbl (apl (smb "SMB") db0))

 parent = smb "parent"
 gdparent = smb "gdparent"
 allan = smb "allan"
 brenda = smb "brenda"
 charles = smb "charles"

 gpRule1 = lambda "x" $ lambda "y" $ lambda "z" $ 
  equ (apl (apl2 parent (var "x") (var "y")) $
       apl (apl2 parent (var "y") (var "z")) $
       apl2 gdparent (var "x") (var "z"))
      ident
 gpAxiom1 = equ (apl2 parent allan brenda) ident
 gpAxiom2 = equ (apl2 parent brenda charles) ident

 gpLemma1c = apl3 gpRule1 allan brenda charles
 gpLemma2c = apl gpAxiom1 $ apl (apl2 parent brenda charles) $ apl2 gdparent allan charles
 gpLemma3c = ltr gpLemma2c gpLemma1c
 gpLemma4c = apl gpAxiom2 $ apl2 gdparent allan charles
 gpLemma5c = ltr gpLemma4c gpLemma3c
 gpLemma6c = ltr gpLemma4c gpLemma4c
 gpTheorem1c = ltr gpLemma6c gpLemma5c

 gpTheorem1str = "\
\ LET gpRule1 \
\  LBD x LBD y LBD z \
\  EQU APL APL APL parent x y \
\      APL APL APL parent y z \
\      APL APL gdparent x z \
\  DBL DB0 \
\ LET gpAxiom1 EQU APL APL parent allan brenda DBL DB0 \
\ LET gpAxiom2 EQU APL APL parent brenda charles DBL DB0 \
\ LET gpLemma1 APL APL APL gpRule1 allan brenda charles \
\ LET gpLemma2 APL gpAxiom1 APL APL APL parent brenda charles APL APL gdparent allan charles \
\ LET gpLemma3 LTR gpLemma2 gpLemma1 \
\ LET gpLemma4 APL gpAxiom2 APL APL gdparent allan charles \
\ LTR gpLemma4 gpLemma3 \
\"

 gpTheorem1slc = slc gpTheorem1str

 gpTheorem2slc = slc "\
\ LET gpRule1 \
\  LBD x LBD y LBD z \
\  EQU APL APL APL parent x y \
\      APL APL APL parent y z \
\      APL APL gdparent x z \
\  DBL DB0 \
\ LET gpAxiom1 EQU APL APL parent allan brenda DBL DB0 \
\ LET gpAxiom2 EQU APL APL parent brenda charles DBL DB0 \
\ LTR \
\  APL gpAxiom2 APL APL gdparent allan charles \
\  LTR \
\   APL gpAxiom1 APL APL APL parent brenda charles APL APL gdparent allan charles \
\   APL APL APL gpRule1 allan brenda charles \
\"
 

 imp = smb "imp"
 false = smb "false"
 al = smb "all"
 some = smb "some"
 p = smb "p"

 propMp = lambda "p" $ lambda "q" $ equ (apl (apl2 imp (var "p") (var "q")) $ apl (var "p") (var "q")) ident
 propAk = lambda "p" $ lambda "q" $ equ (apl2 imp (var "p") (apl2 imp (var "q") (var "p"))) ident
 propAs = lambda "p" $ lambda "q" $ lambda "r" $ 
  equ (apl2 imp (apl2 imp (var "p") (apl2 imp (var "q") (var "r"))) (apl2 imp (apl2 imp (var "p") (var "q")) (apl2 imp (var "p") (var "r")))) ident
 propEfq = lambda "p" $ equ (apl2 imp false (var "p")) ident 
 propRaa = lambda "p" $ equ (apl2 imp (apl2 imp (apl2 imp (var "p") false) false) (var "p")) ident
 predGen = lambda "p" $ equ (apl (var "p") (apl al (dbl (var "p")))) ident
 predPart = lambda "p" $ lambda "t" $ equ (apl2 imp (apl al (var "p")) (apl (var "p") (var "t"))) ident
 predPermut = lambda "p" $ lambda "q" $ equ (apl2 imp (apl al $ lambda "x" $ apl2 imp (var "p") (apl (var "q") (var "x"))) (apl2 imp (var "p") (apl al (var "q")))) ident
 predSome = lambda "p" $ equ (apl2 imp (apl2 imp (apl al (var "p")) false) (apl2 imp (apl (var "p") (apl some $ lambda "x" $ apl2 imp (apl (var "p") (var "x")) false)) false)) ident

 propLemma1 = apl3 propAs p (apl2 imp p p) p
 propLemma2 = apl2 propAk p (apl2 imp p p)
 propLemma3 = apl2 propMp (apl2 imp p (apl2 imp (apl2 imp p p) p)) (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma4 = apl propLemma1 (apl (apl2 imp p (apl2 imp (apl2 imp p p) p)) (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p)))
 propLemma5 = ltr propLemma4 propLemma3
 propLemma6 = apl propLemma2 (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma7 = ltr propLemma6 propLemma5
 propLemma8 = apl2 propAk p p
 propLemma9 = apl2 propMp (apl2 imp p (apl2 imp p p)) (apl2 imp p p)
 propLemma10 = apl propLemma7 (apl (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma11 = ltr propLemma10 propLemma9
 propLemma12 = apl propLemma8 (apl2 imp p p)
 -- propTheorem1 = LTR propLemma12 propLemma11
 propLemma13 = ltr propLemma12 propLemma12
 propLemma14 = ltr propLemma12 propLemma11
 propTheorem1 = ltr propLemma13 propLemma14 

 a = smb "a"
 b = smb "b"
 c = smb "c"
 d = smb "d"

 ltr2 = dbl (dbl (ltr (ltr (dbs db0) (dbs db0)) (ltr (dbs db0) db0))) 

 test = do
  proves (ltr (ltr axm (smb "SMB")) (apl (smb "SMB") axm))
  proves (ltr (ltr axm (smb "SMB")) (apl axm (smb "SMB")))
  proves (ltr (ltr axm (smb "SMB")) (apl axm axm))
  reducesTo (apl (apl (dbl db0) (dbl db0)) (apl (dbl db0) (smb "SMB")))
  reducesTo (fix ident)
  reducesTo (fix (dbl (apl (smb "SMB") db0)))  
  proves gpTheorem1c
  proves propTheorem1
  proves (ltr (ltr gpLemma4c gpLemma4c) (ltr gpLemma4c gpLemma3c))


 -- SLC representations of useful data structures and combinators

 slc_true = lambda "t" $ lambda "f" $ var "t"
 slc_false = lambda "t" $ lambda "f" $ var "f"

 slc_pair = lambda "x" $ lambda "y" $ lambda "f" $ apl2 (var "f") (var "x") (var "y")
 slc_fst = lambda "p" $ apl (var "p") (lambda "x" $ lambda "y" (var "x"))
 slc_snd = lambda "p" $ apl (var "p") (lambda "x" $ lambda "y" (var "y"))

 slc_K = lambda "x" $ lambda "y" $ var "x"

 slc_leftside = lambda "l" $ lambda "r" $ var "l"
 slc_rightside = lambda "l" $ lambda "r" $ var "r"

 smb1 = smb "SMB"
 sdb0 = smb "sdb0"

 -- SLC representation of SLC proofs

 slc_axm = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  var "axm"

 slc_smb = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  var "smb"

 slc_db0 = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  var "db0"

 slc_dbs = lambda "x" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  apl (var "dbs") (var "x")

 slc_dbl = lambda "x" $
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  apl (var "dbl") (var "x")

 slc_apl = lambda "x" $ lambda "y" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  apl2 (var "apl") (var "x") (var "y") 

 slc_ltr = lambda "x" $ lambda "y" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  apl2 (var "ltr") (var "x") (var "y")

 rep :: Proof -> Proof
 rep (Proof0 AXM) = slc_axm
 rep (Proof0 (SMB s)) = slc_smb
 rep (Proof0 DB0) = slc_db0
 rep (Proof1 DBS x) = apl slc_dbs (rep x)
 rep (Proof1 DBL x) = apl slc_dbl (rep x)
 rep (Proof2 APL x y) = apl2 slc_apl (rep x) (rep y)
 rep (Proof2 LTR x y) = apl2 slc_ltr (rep x) (rep y)
 rep _ = slc_smb

 -- SLC definitions of previously defined Haskell functions

 slc_rep = fix $ lambda "rep" $ lambda "x"$ apl7 (var "x")
  (rep slc_axm)
  (rep slc_smb)
  (rep slc_db0)
  (lambda "x1" $ apl2 slc_apl (rep slc_dbs) (apl (var "rep") (var "x1")))
  (lambda "x1" $ apl2 slc_apl (rep slc_dbl) (apl (var "rep") (var "x1")))
  (lambda "x1" $ lambda "y1" $ apl2 slc_apl (apl2 slc_apl (rep slc_apl) (apl (var "rep") (var "x1"))) (apl (var "rep") (var "y1")))
  (lambda "x1" $ lambda "y1" $ apl2 slc_apl (apl2 slc_apl (rep slc_ltr) (apl (var "rep") (var "x1"))) (apl (var "rep") (var "y1")))

 slc_equal = fix $ lambda "equal" $ lambda "x" $ lambda "y" $ 
  apl7 (var "x") 
   (apl7 (var "y") slc_true  slc_false slc_false (apl slc_K slc_false) (apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false))
   (apl7 (var "y") slc_false slc_true  slc_false (apl slc_K slc_false) (apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false))
   (apl7 (var "y") slc_false slc_false slc_true  (apl slc_K slc_false) (apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false))
   (lambda "a" $ 
    apl7 (var "y") slc_false slc_false slc_false (apl (var "equal") (var "a")) 
                                                                       (apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false))
   (lambda "a" $
    apl7 (var "y") slc_false slc_false slc_false (apl slc_K slc_false) (apl (var "equal") (var "a"))
                                                                                             (apl slc_K $ apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false))
   (lambda "x1" $ lambda "x2" $
    apl7 (var "y") slc_false slc_false slc_false (apl slc_K slc_false) (apl slc_K slc_false) 
    (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) slc_false)
                                                                                                                               (apl slc_K $ apl slc_K slc_false))
   (lambda "x1" $ lambda "x2" $ 
    apl7 (var "y") slc_false slc_false slc_false (apl slc_K slc_false) (apl slc_K slc_false) (apl slc_K $ apl slc_K slc_false) 
    (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) slc_false)
   )

 slc_shift = fix $ lambda "shift" $ lambda "u" $ lambda "x" $ 
  apl2 (apl2 slc_equal (var "x") (var "u")) (apl slc_dbs (var "u")) $
  apl7 (var "x")
   slc_axm
   slc_smb
   slc_db0
   (lambda "x1" $ apl slc_dbs $ apl2 (var "shift") (var "u") (var "x1"))
   (lambda "x1" $ apl slc_dbl $ apl2 (var "shift") (apl slc_dbs (var "u")) (var "x1"))
   (lambda "x1" $ lambda "x2" $ apl2 slc_apl (apl2 (var "shift") (var "u") (var "x1")) (apl2 (var "shift") (var "u") (var "x2")))
   (lambda "x1" $ lambda "x2" $ apl2 slc_ltr (apl2 (var "shift") (var "u") (var "x1")) (apl2 (var "shift") (var "u") (var "x2")))

 slc_subst = fix $ lambda "subst" $ lambda "u" $ lambda "a" $ lambda "b" $
  apl2 (apl2 slc_equal (var "a") (var "u")) (var "b") $
  apl7 (var "a")
   slc_axm
   slc_smb
   slc_db0
   (lambda "a1" $ apl2 (apl2 slc_equal (var "a1") (var "u")) (var "u") $ apl slc_dbs $ apl3 (var "subst") (var "u") (var "a1") (var "b"))
-- (lambda "a1" $ apl slc_dbl $ apl3 (var "subst") (apl slc_dbs (var "u")) (var "a1") (apl2 slc_shift slc_db0 (var "b")))
   (lambda "a1" $ apl slc_dbl $ apl3 (var "subst") (apl slc_dbs (var "u")) (var "a1") (apl2 slc_shift (var "u") (var "b")))
   (lambda "a1" $ lambda "a2" $ apl2 slc_apl (apl3 (var "subst") (var "u") (var "a1") (var "b")) 
                                          (apl3 (var "subst") (var "u") (var "a2") (var "b")) )
   (lambda "a1" $ lambda "a2" $ apl2 slc_ltr (apl3 (var "subst") (var "u") (var "a1") (var "b")) 
                                          (apl3 (var "subst") (var "u") (var "a2") (var "b")) )

 slc_red1 = fix $ lambda "red1" $ lambda "x" $
  apl7 (var "x") 
   -- x = AXM
   slc_axm
   -- x = SMB
   slc_smb
   -- x = DB0
   slc_db0
   -- x = DBS x1
   (lambda "x1" $ apl slc_dbs $ apl (var "red1") (var "x1"))
   -- x = DBL x1
   (lambda "x1" $ apl slc_dbl $ apl (var "red1") (var "x1"))
   -- x = APL x1 y1
   (lambda "x1" $ lambda "y1" $ apl7 (var "x1") 
    -- x1 = AXM
    (apl2 slc_apl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    -- x1 = SMB
    (apl2 slc_apl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    -- x1 = DB0
    (apl2 slc_apl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    -- x1 = DBS _
    -- (apl slc_K $ apl2 slc_apl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    (apl slc_K $
     apl (lambda "x2" $ 
          apl4 slc_equal (var "x1") (var "x2") 
           (apl2 slc_apl (var "x2") (apl (var "red1") (var "y1"))) 
           (apl2 slc_apl (var "x2") (var "y1")))
      (apl (var "red1") (var "x1")) )
    -- x1 = DBL x2
    (lambda "x2" $ apl3 slc_subst slc_db0 (var "x2") (var "y1"))
    -- x1 = APL _ _
    -- (apl slc_K $ apl slc_K $ apl2 slc_apl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    (apl slc_K $ apl slc_K $
     apl (lambda "x2" $ 
          apl4 slc_equal (var "x1") (var "x2") 
           (apl2 slc_apl (var "x2") (apl (var "red1") (var "y1"))) 
           (apl2 slc_apl (var "x2") (var "y1")))
      (apl (var "red1") (var "x1")) )
    -- x1 = LTR _ _
    -- (apl slc_K $ apl slc_K $ apl2 slc_apl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1"))))
    (apl slc_K $ apl slc_K $
     apl (lambda "x2" $ 
          apl4 slc_equal (var "x1") (var "x2") 
           (apl2 slc_apl (var "x2") (apl (var "red1") (var "y1"))) 
           (apl2 slc_apl (var "x2") (var "y1")))
      (apl (var "red1") (var "x1")) ) )
   -- x = LTR x y
   -- (lambda "x1" $ lambda "x2" $ apl2 slc_ltr (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
   (lambda "x1" $ lambda "y1" $ 
    apl (lambda "x2" $ 
         apl4 slc_equal (var "x1") (var "x2") 
          (apl2 slc_ltr (var "x2") (apl (var "red1") (var "y1"))) 
          (apl2 slc_ltr (var "x2") (var "y1")) )
     (apl (var "red1") (var "x1")) )

 slc_red = fix $ lambda "red" $ lambda "x" $
  apl (lambda "y" $ apl2 (apl2 slc_equal (var "x") (var "y")) (var "x") (apl (var "red") (var "y"))) (apl slc_red1 (var "x"))

 slc_side = fix $ lambda "side" $ lambda "s" $ lambda "u" $ lambda "v" $ lambda "x" $ apl7 (var "x") 
  (apl2 (var "s") (var "u") (var "v"))
  slc_smb
  slc_db0
  (lambda "x1" $ apl slc_dbs $ apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
  (lambda "x1" $ apl slc_dbl $ apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
  (lambda "x1" $ lambda "x2" $ apl2 slc_apl (apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
                                         (apl4 (var "side") (var "s") (var "u") (var "v") (var "x2")))
  (lambda "x1" $ lambda "x2" $ 
   apl2 (apl2 slc_equal (apl slc_red $ apl4 (var "side") slc_leftside (var "u") (var "v") (var "x1"))
                     (apl slc_red $ apl4 (var "side") slc_leftside (var "u") (var "v") (var "x2")))
    (apl slc_red $ apl4 (var "side") slc_rightside (var "u") (var "v") (apl2 (var "s") (var "x1") (var "x2")))
    (apl2 slc_ltr (var "x1") (var "x2")))

 switchside LeftSide u v = u
 switchside RightSide u v = v


 -- Reflection

 slc_mapproof = fix $ lambda "mapproof" $ lambda "f" $
  lambda "x" $ apl7 (var "x") 
   (apl (var "f") slc_axm)
   (apl (var "f") slc_smb)
   (apl (var "f") slc_db0)
   (apl (var "mapproof") $ lambda "x1" $ apl (var "f") $ apl slc_dbs (var "x1"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "f") $ apl slc_dbl (var "x1"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 slc_apl (var "x1") (var "x2"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 slc_ltr (var "x1") (var "x2"))

 slc_zero = lambda "z" $ lambda "s" (var "z")
 slc_succ = lambda "n" $ lambda "z" $ lambda "s" $ apl (var "s") (var "n")

 slc_mapnat = fix $ lambda "mapnat" $ lambda "f" $
  lambda "n" $ apl2 (var "n")
   (apl (var "f") slc_zero)
   (apl (var "slc_mapnat") $ lambda "n1" $ apl (var "f") $ apl slc_succ (var "n1"))
   

 -- Evaluation of the representation of a SLC proof

 slc_eva = fix $ lambda "eva" $ lambda "x" $ lambda "u" $ apl7 (var "x")
  axm
  smb1 
  (var "u")
  (lambda "x1" $ dbs $ apl2 (var "eva") (var "x1") (var "u"))
  (lambda "x1" $ dbl $ apl2 (var "eva") (var "x1") db0)
  (lambda "x1" $ lambda "y1" $ apl (apl2 (var "eva") (var "x1") (var "u")) (apl2 (var "eva") (var "y1") (var "u")))
  (lambda "x1" $ lambda "y1" $ ltr (apl2 (var "eva") (var "x1") (var "u")) (apl2 (var "eva") (var "y1") (var "u")))

 slc_eval = lambda "x" $ apl2 slc_eva (var "x") (dbs db0)


 -- u, v = representation of left and right sides of axiom
 slc_lrefl = lambda "u" $ lambda "v" $ apl slc_mapproof $ lambda "rp" $ apl slc_eval $ apl4 slc_side slc_leftside (var "u") (var "v") (var "rp")
 slc_rrefl = lambda "u" $ lambda "v" $ apl slc_mapproof $ lambda "rp" $ apl slc_eval $ apl4 slc_side slc_rightside (var "u") (var "v") (var "rp")
 slc_refl = lambda "s" $ lambda "u" $ lambda "v" $ apl slc_mapproof $ lambda "rp" $ apl slc_eval $ apl4 slc_side (var "s") (var "u") (var "v") (var "rp")

 -- a theory is represented by the pair ( l , r )
 -- adding reflection gives a new theory represented by ( l1, r1 )
 -- with l1 = apl2 slc_pair l (apl2 slc_lrefl rl rr)
 -- and  r1 = apl2 slc_pair r (apl2 slc_rrefl rl rr)
 -- with rl = rep l
 -- and  rr = rep r

 -- a theory is represented by l and r ( axiom l = r )
 
 lreflex l r = apl2 slc_lrefl (rep l) (rep r) 
 rreflex l r = apl2 slc_rrefl (rep l) (rep r)

 sreflex LeftSide l r = lreflex l r
 sreflex RightSide l r = rreflex l r

 laddrefl l r = apl2 slc_pair l (lreflex l r)
 raddrefl l r = apl2 slc_pair r (rreflex l r)

 -- Add reflection to a theory
 -- t = ( l , r )
 addrefl t = ( laddrefl (fst t) (snd t) , raddrefl (fst t) (snd t) )


 -- t = ( l , r )
 -- l = fst t ; r = snd t
 -- t' = addrefl t = ( l1 , r1 )
 --  = ( laddrefl l0 r0 , raddrefl l0 r0 
 --  = ( apl2 slc_pair l (lreflex l r), 
 --      apl2 slc_pair r (rreflex l r) )
 --  = ( apl2 slc_pair l (apl2 slc_lrefl (rep l) (rep r)) ,
 --      apl2 slc_pair r (apl2 slc_rrefl (rep l) (rep r) )
 --  = ( apl2 slc_pair l (apl slc_mapproof $ lambda "rp" $
 --                    apl slc_eval $ apl4 slc_side slc_leftside (rep l) (rep r) (var "rp") ) ,
 --      apl2 slc_pair r (apl slc_mapproof $ lambda "rp" $
 --                    apl slc_eval $ apl4 slc_side slc_rightside (rep l) (rep r) (var "rp") ) )

 -- Finite iteration of reflection principle
 firp t n = if (n <= 0) then t else addrefl t

 -- mapnat f = < f 0, < f 1, < f 2, ... >>>
 -- with < a , b > = apl2 slc_pair a b
 
 -- a theory is represented by the pair t = < rl , rr > = apl2 slc_pair rl rr 
 -- where rl and rr are representations of left and right sides of axiom l and r
 -- adding reflection gives a new theory represented by < rl1 , rr1 > = apl2 slc_pair rl1 rr1
 -- with rl1 = representation of pair < l , slc_lrefl rl rr >
 -- and  rr1 = representation of pair < r , slc_rrefl rl rr >
 -- representation of pair < a , b > with representation of a = ra and representation of b = rb :
 -- slc_pair a b = dbl (apl2 db0 a b) = dbl (apl (apl db0 a) b)
 -- slc_rpair ra rb = apl slc_dbl (apl2 slc_apl (apl2 slc_apl slc_db0 ra) rb)

 slc_rpair = lambda "ra" $ lambda "rb" $
  apl slc_dbl $ apl2 slc_apl (apl2 slc_apl slc_db0 (var "ra")) (var "rb")

{-
 slc_addrefl = lambda "t" $
  apl2 slc_pair (apl2 slc_rpair (apl (var "t") slc_true)  (rep $ apl2 slc_lrefl (apl (var "t") slc_true) (apl (var "t") slc_false)))
             (apl2 slc_rpair (apl (var "t") slc_false) (rep $ apl2 slc_rrefl (apl (var "t") slc_true) (apl (var "t") slc_false)))
-}

 -- conversion rules Haskell function -> SLC function
 -- non recursive function definition :
 -- f x1 ... xn = ... -> mf = lambda "x1" $ ... lambda "xn" $ ...
 -- recursive function definition :
 -- f x1 ... xn = ... -> mf = fix $ lambda "x1 $ ... lambda "xn" $ ...
 -- non recursive function call :
 -- f(x1, ..., xn) ->  apln mf (var "x1") ... (var "xn")
 -- recursive call :
 -- f(x1, ..., xn) -> apln (var "f") (var "x1") ... (var "xn")
 -- axm -> slc_axm
 -- dbs x -> apl slc_dbs (var "x")
 -- apl x y -> apl2 slc_apl (var "x") (var "y")
 -- SLC proof :
 -- p -> rep p
 -- (x, y) -> apl2 slc_pair (var "x") (var "y")
 -- if x == y then ... else ... -> apl4 slc_equal (var "x") (var "y") ... ...

 -- laddrefl l r = apl (apl slc_pair l) (lreflex l r)
 --  = apl (apl slc_pair l) (apl (apl slc_lrefl (rep l)) (rep r))

 slc_laddrefl = lambda "l" $ lambda "r" $ 
  apl2 slc_apl (apl2 slc_apl (rep slc_pair) (var "l"))
            (apl2 slc_apl (apl2 slc_apl (rep slc_lrefl) (apl slc_rep (var "l"))) (apl slc_rep (var "r")))

 slc_raddrefl = lambda "l" $ lambda "r" $ 
  apl2 slc_apl (apl2 slc_apl (rep slc_pair) (var "l"))
            (apl2 slc_apl (apl2 slc_apl (rep slc_rrefl) (apl slc_rep (var "l"))) (apl slc_rep (var "r")))

 slc_addrefl = lambda "t" $ 
  apl2 slc_pair (apl2 slc_laddrefl (apl slc_fst (var "t")) (apl slc_snd (var "t")))
             (apl2 slc_raddrefl (apl slc_fst (var "t")) (apl slc_snd (var "t")))

 slc_rptaddrefl = fix $ lambda "rptaddrefl" $ lambda "t" $ lambda "n" $
  apl2 (var "n")
   (var "t")
   (lambda "n1" $ apl slc_addrefl $ apl2 (var "rptaddrefl") (var "t") (var "n1"))

{-
 slc_fl = lambda "l" $ lambda "r" $ lambda "n" $
  apl (lambda "tn" $ apl slc_fst (var "tn"))
   (apl2 slc_rptaddrefl (apl2 slc_pair (var "l") (var "r")) (var "n"))

 slc_fr = lambda "l" $ lambda "r" $ lambda "n" $
  apl (lambda "tn" $ apl slc_snd (var "tn"))
   (apl2 slc_rptaddrefl (apl2 slc_pair (var "l") (var "r")) (var "n"))
-}

 slc_fl = lambda "l" $ lambda "r" $ lambda "n" $
  apl slc_fst $
  apl2 slc_rptaddrefl (apl2 slc_pair (var "l") (var "r")) (var "n") 

 slc_fr = lambda "l" $ lambda "r" $ lambda "n" $
  apl slc_snd $
  apl2 slc_rptaddrefl (apl2 slc_pair (var "l") (var "r")) (var "n")

 slc_flt = lambda "t" $ lambda "n" $
  apl slc_fst $
  apl2 slc_rptaddrefl (var "t") (var "n")

 slc_frt = lambda "t" $ lambda "n" $
  apl slc_snd $
  apl2 slc_rptaddrefl (var "t") (var "n")

{-
 slc_tw = lambda "t" $
  apl2 slc_pair (apl slc_mapnat $ lambda "n" $ apl3 slc_fl (apl slc_fst (var "t")) (apl slc_snd (var "t")) (var "n"))
             (apl slc_mapnat $ lambda "n" $ apl3 slc_fr (apl slc_fst (var "t")) (apl slc_snd (var "t")) (var "n"))

 slc_tw = lambda "t" $
  apl2 slc_pair (apl slc_mapnat $ lambda "n" $ apl3 slc_flt (var "t") (var "n"))
             (apl slc_mapnat $ lambda "n" $ apl3 slc_frt (var "t") (var "n"))
-}

 slc_tw = lambda "t" $
  apl2 slc_pair (apl slc_mapnat $ lambda "n" $ apl slc_fst $ apl2 slc_rptaddrefl (var "t") (var "n"))
             (apl slc_mapnat $ lambda "n" $ apl slc_snd $ apl2 slc_rptaddrefl (var "t") (var "n"))

 -- modify slc_rptaddrefl and slc_tw by replacing slc_addrefl by parameter function

 slc_rptf = fix $ lambda "rptf" $ lambda "f" $ lambda "t" $ lambda "n" $
  apl2 (var "n")
   (var "t")
   (lambda "n1" $ apl (var "f") $ apl3 (var "rptf") (var "f") (var "t") (var "n1"))

 slc_tfw = lambda "f" $ lambda "t" $ 
  apl2 slc_pair (apl slc_mapnat $ lambda "n" $ apl slc_fst $ apl3 slc_rptf (var "f") (var "t") (var "n"))
             (apl slc_mapnat $ lambda "n" $ apl slc_snd $ apl3 slc_rptf (var "f") (var "t") (var "n"))

 slc_tw1 = apl slc_tfw slc_addrefl
 slc_tw2 = apl slc_tfw slc_tw1 -- w^2
 slc_tw3 = apl slc_tfw slc_tw2 -- w^3


 data Nat =
    ZeroN
  | SucN Nat

 data Ordi =
    Zero
  | Suc Ordi
  | Lim (Nat -> Ordi)

 rpt ZeroN f x = x
 rpt (SucN n) f x = rpt n f (f x)

 fixpt f x = Lim (\n -> rpt n f x)

 w = fixpt Suc Zero

{-
 tirp :: (Proof,Proof) -> Ordi -> (Proof,Proof)
 tirp t Zero = t
 tirp t (Suc x) = addrefl (tirp t x)
 tirp t (Lim f) = ...
-}

 -- Representation of transfinite ordinals in SLC
 slc_ordZero = lambda "z" $ lambda "s" $ lambda "l" (var "z")
 slc_ordSuc = lambda "x" $ lambda "z" $ lambda "s" $ lambda "l" $ apl (var "s") (var "x")
 slc_ordLim = lambda "f" $ lambda "z" $ lambda "s" $ lambda "l" $ apl (var "l") (var "f")

 slc_rpt = fix $ lambda "rpt" $ lambda "n" $ lambda "f" $ lambda "x" $
  apl2 (var "n")
   (var "x")
   (apl3 (var "rpt") (var "n") (var "f") (apl (var "f") (var "x")))

 slc_fixpt = lambda "f" $ lambda "x" $ apl slc_ordLim (lambda "n" $ apl3 slc_rpt (var "n") (var "f") (var "x"))

 slc_w = apl2 slc_fixpt slc_ordSuc slc_ordZero

 slc_limt = lambda "f" $
  apl2 slc_pair
   (apl slc_mapnat $ lambda "n" $ apl slc_fst $ apl (var "f") (var "n"))
   (apl slc_mapnat $ lambda "n" $ apl slc_snd $ apl (var "f") (var "n"))

 -- Transfinite iteration of reflection principle applied "x times" to theory t
 slc_tirp = fix $ lambda "tirp" $ lambda "t" $ lambda "x" $ 
  apl3 (var "x")
   (var "t")
   (lambda "x1" $ apl slc_addrefl (apl2 (var "tirp") (var "t") (var "x")))
   (lambda "f" $ apl slc_limt $ lambda "n" $ apl2 (var "tirp") (var "t") (apl (var "f") (var "n")))
   
   -- (lambda "f" $ apl2 slc_tfw (var "f") (var "t")) 
   


