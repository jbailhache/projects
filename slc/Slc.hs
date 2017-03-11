module Slc where

 import Data.List
 import Data.Char

 data Proof = Proof0 Rule0 | Proof1 Rule1 Proof | Proof2 Rule2 Proof Proof

 data Rule0 = AXM | DB0 | SMB String 

 data Rule1 = DBS | DBL 
  deriving (Eq)

 data Rule2 = EQU | APL | LTR 
  deriving (Eq)

 instance Eq Proof where
  Proof0 AXM == Proof0 AXM = True
  Proof0 DB0 == Proof0 DB0 = True
  Proof0 (SMB s1) == Proof0 (SMB s2) = s1 == s2
  Proof1 r1 x1 == Proof1 r2 x2 = r1 == r2 && x1 == x2
  Proof2 r1 x1 y1 == Proof2 r2 x2 y2 = r1 == r2 && x1 == x2 && y1 == y2
  _ == _ = False

 instance Show Rule0 where
  show AXM = "AXM"
  -- show DB0 = "DB0"
  show DB0 = "*"
  show (SMB s) = s

 instance Show Rule1 where
  -- show DBS = "+"
  show DBS = "'"
  -- show DBP = "P"
  show DBL = "\\"

 instance Show Rule2 where
  show EQU = "="
  show APL = "-"
  -- show LTR = "&"
  show LTR = "LTR"
 
 -- dbv = Proof1 NXT $ Proof0 DB0
 dbv = Proof0 DB0

 axm = Proof0 AXM
 -- db0 = Proof0 DB0
 db0i = Proof0 DB0
 db0 = dbv
 smb s = Proof0 (SMB s)
 dbs x = Proof1 DBS x
 dbl x = Proof1 DBL x
 -- dbl x = Proof2 LBD (Proof0 DB0) x
 dbli x = Proof1 DBL x
 -- dbl x = Proof2 LBD dbv x
 equ x y = Proof2 EQU x y
 apl x y = Proof2 APL x y
 ltr x y = Proof2 LTR x y


 apply (Proof1 DBL (Proof0 DB0)) y = y
 apply x y = apl x y

 showapl (Proof2 APL x y) (Proof2 APL z t) True = showapl x y True ++ " : " ++ showapl z t True
 showapl (Proof2 APL x y) (Proof2 APL z t) False = showapl x y False ++ " (" ++ showapl z t True ++ ")"
 showapl (Proof2 APL x y) z _ = showapl x y False ++ " " ++ show z
 showapl x (Proof2 APL y z) True = show x ++ " : " ++ showapl y z True
 showapl x (Proof2 APL y z) False = show x ++ " (" ++ showapl y z True ++ ")"
 showapl x y _ = show x ++ " " ++ show y

 showproof (Proof0 (SMB s)) = s
 showproof (Proof1 DBL (Proof2 APL x y)) = "[" ++ showapl x y True ++ "]"
 showproof (Proof1 DBL x) = "[" ++ showproof x ++ "]"
 showproof (Proof2 APL x y) = "(" ++ showapl x y True ++ ")"
 showproof (Proof0 r) = show r
 showproof (Proof1 r x) = show r ++ showproof x
 -- showproof (Proof1 r x) = show r ++ " " ++ showproof x
 showproof (Proof2 r x y) = show r ++ " " ++ showproof x ++ " " ++ showproof y

 instance Show Proof where
  show x = showproof x


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
  slc "= (parent brenda charles) \\@",
  smb "parent",
  smb "gdparent",
  smb "allan",
  smb "brenda",
  smb "charles"]

 naxm = length axioms

 -- nthproof 0 = axm
 nthproof n = if n < naxm then axioms !! n else nthproof1 (n - naxm)

 -- nthproof1 0 = axm
 nthproof1 0 = db0
 -- nthproof1 1 = smb "SMB"
 nthproof1 (n+1) = let p = div n 4 in case mod n 4 of
  0 -> dbs $ nthproof p
  1 -> dbl $ nthproof p
  2 -> apl (nthproof $ first p) (nthproof $ second p)
  3 -> ltr (nthproof $ first p) (nthproof $ second p)

 show1 x = show x ++ "  proves  " ++ show (left x) ++ "  ==  " ++ show (right x) ++ "\n"

 show_proofs n 0 = ""
 show_proofs n (p+1) = show n ++ ": " ++ show1 (nthproof n) ++ "\n" ++ show_proofs (n+1) p

 display_proofs n = putStr (show_proofs 0 n)

 prove a b = prove1 0 a b

 prove1 n a b = let x = nthproof n in if (left x == a) && (right x == b) then (n, x) else prove1 (n+1) a b

 testprove = prove (slc "gdparent allan charles") (dbl db0)


 first_size s = first_size1 0 s

 first_size1 n s = let s1 = size (nthproof n) in if s1 >= s then (n,s1) else first_size1 (n+1) s


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


 slc1 ("AXM" : s) e = (axm, s)
 slc1 ("DB0" : s) e = (db0, s)
 slc1 ("$"   : s) e = (db0, s)
 slc1 ("@"   : s) e = (db0, s)
 slc1 ("*"   : s) e = (db0, s)
 slc1 ("DBS" : s) e = let (x, t) = slc1 s e in (dbs x, t)
 slc1 ("+"   : s) e = let (x, t) = slc1 s e in (dbs x, t)
 slc1 ("'"   : s) e = let (x, t) = slc1 s e in (dbs x, t)
 slc1 ("DBL" : s) e = let (x, t) = slc1 s e in (dbl x, t)
 slc1 ("\\"  : s) e = let (x, t) = slc1 s e in (dbl x, t)
 slc1 ("/"   : s) e = let (x, t) = slc1 s e in (dbl x, t)
 slc1 ("APL" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (apl x y, u)
 slc1 ("-"   : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (apl x y, u)
 slc1 ("LTR" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (ltr x y, u)
 slc1 ("&"   : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (ltr x y, u)
 slc1 ("EQU" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (equ x y, u)
 slc1 ("="   : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (equ x y, u)
 slc1 ("LET" : v : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (apply (lambda v y) x, u)
 -- slc1 (":"   : v : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (apl (lambda v y) x, u)
 slc1 ("LBD" : v : s) e = let (x, t) = slc1 s e in (lambda v x, t)
 slc1 ("^"   : v : s) e = let (x, t) = slc1 s e in (lambda v x, t)
 slc1 ("("   : s) e = slc2 s ")" (dbl db0) False 
 slc1 (":"   : s) e = slc2 s e (dbl db0) True
 slc1 ("["   : s) e = let (x, t) = slc2 s "]" (dbl db0) False in (dbl x, t)

 slc1 (w : s) e = (smb w, s)


 slc2 (w : t) e x c =
  if w == e then
   case c of
    False -> (x, t)
    True -> (x, w : t)
  else
   slc3 (w : t) e x c
 slc2 s e x c = slc3 s e x c
 slc3 s e (Proof1 DBL (Proof0 DB0)) c = let (y, t) = slc1 s e in slc2 t e y c
 slc3 s e x c = let (y, t) = slc1 s e in slc2 t e (apl x y) c


 blank = " \t\n"
 delim = "@$*'\\/^()[]"

 slc s = let (x, t) = slc1 (split blank delim ("( " ++ s ++ " )")) ")" in if t == [] || head t == "" then x else smb ("Error : Unexpected '" ++ concat (map (\x -> x ++ " ") t) ++ "'")

 -- slc s = let (x, t) = slc2 (split " \t\n" s) [] in if t == [] || head t == "" then x else smb ("Error : Unexpected '" ++ concat (map (\x -> x ++ " ") t) ++ "'")


 size :: Proof -> Int
 size (Proof0 r) = 1
 size (Proof1 r x) = 1 + (size x)
 size (Proof2 r x y) = 1 + (size x) + (size y)

 data Side = LeftSide | RightSide
  deriving (Eq, Show)

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

 red1 :: Proof -> Proof
 red1 (Proof2 APL (Proof1 DBL x) y) = subst (Proof0 DB0) x y
 -- red1 (Proof2 APL (Proof1 DBL x) y) = subst (Proof0 DB0) (red1 x) (red1 y)
 -- red1 (Proof1 DBS (Proof1 DBP x)) = x
 red1 (Proof0 r) = Proof0 r
 red1 (Proof1 r x) = Proof1 r (red1 x)
 -- red1 (Proof2 r x y) = Proof2 r (red1 x) (red1 y)
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

 reduce :: Proof -> Proof
 reduce x = case red3 (x : []) of
		[] -> x
		y : m -> y
 -- reduce x = if red1 x == x then x else reduce (red1 x)

 r = reduce

 rered1 :: Int -> Proof -> Proof
 rered1 n x = if (n == 0) then x else rered1 (n - 1) (red1 x)

 rered1xn x n = rered1 n x

 side :: Side -> Proof -> Proof -> Proof -> Proof
 -- AXM |- u = v
 side LeftSide u v (Proof0 AXM) = u
 side RightSide u v (Proof0 AXM) = v
 -- EQU : a, b |- a = b
 side LeftSide _ _ (Proof2 EQU x y) = x
 side RightSide _ _ (Proof2 EQU x y) = y
 -- APL : reduce ; a = b, c = d |- a c = b d
 -- side s u v (Proof2 APL x y) = side s u v (reduce (Proof2 APL x y))
 -- Uncomment 5 lines below to activate APL reduction
 -- side s u v (Proof2 APL x y) = 
 --  let z = reduce (Proof2 APL x y) in
 --  if z == Proof2 APL x y
 --  then Proof2 APL (side s u v x) (side s u v y)
 --  else side s u v z
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
 -- lambda v x = dbl (abstr db0 v x)
 lambda v x = dbl (abstr dbv v x)

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
  -- putStr ("\n  " ++ show x ++ "\nreduces to\n  " ++ show (reduce x) ++ "\n")
  putStr ("\n" ++ show x ++ "\nreduces to\n" ++ show (reduce x) ++ "\n")

{-
 pr1 x y = do
  putStr ("\nThe proof\n" ++ show x ++ "\nreduces to\n" ++ show y ++ "\nwhich proves\n" ++ show (left y) ++ "\nequals\n" ++ show (right y) ++ "\n")

 pr x = do
  pr1 x (reduce x)
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


 run1 filename = do
  readFile filename >>= \s -> proves $ slc s

 run filename = do
  -- readFile filename >>= \s -> proves $ slc s
  -- readFile filename >>= \s -> proves (let x = slc s in ltr x x)
  -- readFile filename >>= \s -> proves $ reduce $ slc s
  readFile filename >>= \s -> pr $ slc s

 check filename = do
  readFile filename >>= \s -> proves $ slc s

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

 gpRule1s = slc "\
\ LBD x LBD y LBD z \
\ EQU APL APL APL parent x y \
\     APL APL APL parent y z \
\     APL APL gdparent x y \
\ DBL DB0 \
\"
 
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
 
 gpTest1str = "\
\ LET gpRule1 \
\  LBD x LBD y LBD z \
\  EQU APL APL APL parent x y \
\      APL APL APL parent y z \
\      APL APL gdparent x y \
\  DBL DB0 \
\ APL APL APL gpRule1 allan brenda charles \
\"
 
 gpTest1slc = slc gpTest1str

 gpTest2str = "\
\ LET gpRule1 \
\  LBD x LBD y LBD z \
\  EQU APL APL APL parent x y \
\      APL APL APL parent y z \
\      APL APL gdparent x z \
\  DBL DB0 \
\ LET gpAxiom1 EQU APL APL parent allan brenda DBL DB0 \
\ LET gpAxiom2 EQU APL APL parent brenda charles DBL DB0 \
\ LET gpLemma1 APL APL APL gpRule1 allan brenda charles \
\ gpLemma1 \
\"

 gpTest2slc = slc gpTest2str


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

 testSyntaxList [] = do
  -- putStr "Done\n"
  return ()

 testSyntaxList (s : l) = do
  putStr (s ++ " -> " ++ show (slc s) ++ "\n")
  testSyntaxList l

 testSyntax = testSyntaxList [
  "a",
  "a b",
  "a b c",
  "a : b",
  "a : b : c",
  "a (b c) d",
  "a (b : c) d",
  "a (b : c) d : e",
  "a (b : c) (d : e) f",
  "a b c : d e f",
  "a b c : d e f : g h i",
  "a b (c d : e f) g h : i j",
  "a b (c d : e f : g h) i j : k l : m n"
  ]
 

