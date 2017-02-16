module Slcnc where

 import Data.List
 import Data.Char

 data Proof = Proof0 Rule0 | Proof1 Rule1 Proof | Proof2 Rule2 Proof Proof
  -- deriving (Eq)

 data Rule0 = AXM | DB0 | SMB String | FNC (Proof -> Proof)
  -- deriving (Eq)

 data Rule1 = DBS | DBP | NXT | DBL | SYM | RED | RD2 | RDQ | ERQ | LFT | RGT | QOT | RFE | EVL | EVR | NOP
  deriving (Eq)

 data Rule2 = EQU | APL | LTR | LTN | LT2 | LTS | TRN | SUB | LBD
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
  show DB0 = "DB0"
  show (SMB s) = s

 instance Show Rule1 where
  show DBS = "+"
  show DBP = "P"
  show NXT = "*"
  show DBL = "\\"
  show SYM = "SYM"
  show RED = "RED"
  show RD2 = "RD2"
  show RDQ = "RDQ"
  show ERQ = "ERQ"
  show LFT = "LFT"
  show RGT = "RGT"
  show QOT = "QOT"
  show RFE = "RFE"
  show EVL = "EVL"
  show EVR = "EVR"
  show NOP = "NOP"

 instance Show Rule2 where
  show EQU = "="
  show APL = "-"
  show LTR = "&"
  show LTN = "LTN"
  show LT2 = "LT2"
  show LTS = "LTS"
  show TRN = "TRN"
  show SUB = "SUB"
  show LBD = "^"
 
 -- dbv = Proof1 NXT $ Proof0 DB0
 dbv = Proof0 DB0

 axm = Proof0 AXM
 -- db0 = Proof0 DB0
 db0i = Proof0 DB0
 db0 = dbv
 smb s = Proof0 (SMB s)
 dbs x = Proof1 DBS x
 dbp x = Proof1 DBP x
 nxt x = Proof1 NXT x
 dbl x = Proof1 DBL x
 -- dbl x = Proof2 LBD (Proof0 DB0) x
 dbli x = Proof1 DBL x
 -- dbl x = Proof2 LBD dbv x
 sym x = Proof1 SYM x
 red x = Proof1 RED x
 rd2 x = Proof1 RD2 x
 rdq x = Proof1 RDQ x
 erq x = Proof1 ERQ x
 lft x = Proof1 LFT x
 rgt x = Proof1 RGT x
 qot x = Proof1 QOT x
 rfe x = Proof1 RFE x
 evl x = Proof1 EVL x
 evr x = Proof1 EVR x
 nop x = Proof1 NOP x
 equ x y = Proof2 EQU x y
 apl x y = Proof2 APL x y
 ltr x y = Proof2 LTR x y
 ltn x y = Proof2 LTN x y
 lt2 x y = Proof2 LT2 x y
 lts x y = Proof2 LTS x y
 trn x y = Proof2 TRN x y
 sub x y = Proof2 SUB x y
 lbd x y = Proof2 LBD x y

 {-
 instance Show Proof where
  show (Proof0 (SMB s)) = s
  show (Proof0 r) = map toLower(show r) 
  show (Proof1 r x) = "(" ++ map toLower(show r) ++ " " ++ show x ++ ")"
  show (Proof2 r x y) = "(" ++ map toLower(show r) ++ " " ++ show x ++ " " ++ show y ++ ")"
 -}

 {-
 showlevel :: Int -> Proof -> String
 showlevel l (Proof0 (SMB s)) = concat (replicate l "    ") ++ s 
 showlevel l (Proof0 r) = concat (replicate l "    ") ++ show r
 showlevel l (Proof1 r x) = concat (replicate l "    ") ++ show r ++ "\n" ++ showlevel (l+1) x 
 showlevel l (Proof2 r x y) = concat (replicate l "    ") ++ show r ++ "\n" ++ showlevel (l+1) x ++ "\n" ++ showlevel (l+1) y 
 -}

 spaces = "  "
 showlevel :: Int -> Int -> Proof -> String
 showlevel i l (Proof0 (SMB s)) = concat (replicate (i*l) spaces) ++ s 
 showlevel i l (Proof0 (FNC f)) = concat (replicate (i*l) spaces) ++ "FNC"
 showlevel i l (Proof0 r) = concat (replicate (i*l) spaces) ++ show r
 showlevel i l (Proof1 r x) = concat (replicate (i*l) spaces) ++ show r  ++ " " ++ showlevel 0 (l+1) x 
 showlevel i l (Proof2 r x y) = concat (replicate (i*l) spaces) ++ show r ++ " " ++ showlevel 0 (l+1) x ++ "\n" ++ showlevel 1 (l+1) y 

 {-
 showlevel :: Int -> Proof -> String
 showlevel l (Proof0 (SMB s)) = concat (replicate l "    ") ++ s 
 showlevel l (Proof0 r) = concat (replicate l "    ") ++ show r
 showlevel l (Proof1 r x) = concat (replicate l "    ") ++ show r ++ " " ++ showlevel 0 x 
 showlevel l (Proof2 r x y) = concat (replicate l "    ") ++ show r ++ "\n" ++ showlevel (l+1) x ++ "\n" ++ showlevel (l+1) y 
 -}
 instance Show Proof where
  show x = showlevel 1 0 x

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

 compiled :: Proof -> Bool
 compiled (Proof0 (FNC f)) = True
 compiled (Proof0 _) = False
 compiled (Proof1 r x) = compiled x
 compiled (Proof2 r x y) = compiled x || compiled y

 compile1 :: Proof -> Proof
 compile1 (Proof2 APL (Proof0 (FNC f)) y) = f y
 compile1 (Proof1 DBL (Proof0 DB0)) = Proof0 (FNC (\x -> x))
 compile1 (Proof1 DBL x) = if cont x (Proof0 DB0) then (Proof1 DBL (compile1 x)) else Proof0 (FNC (\y -> x))
 -- compile1 (Proof1 DBL (Proof1 DBL (Proof1 DBS (Proof0 DB0)))) = Proof0 (FNC (\x -> \y -> x))
 compile1 (Proof1 DBL (Proof2 APL (Proof0 (FNC f)) (Proof0 DB0))) = Proof0 (FNC f)
 compile1 (Proof1 DBL (Proof2 APL (Proof0 (FNC f)) (Proof2 APL (Proof0 (FNC g)) (Proof0 DB0)))) = Proof0 (FNC (\x -> f (g x)))
{-
 compile1 (Proof1 DBL (Proof2 APL x y)) = 
  let x1 = compile x in
   case x1 of
    Proof0 (FNC f) -> 
     let y1 = compile y in
      case y1 of
       Proof0 (FNC g) -> FNC (\x -> f x (g x))
       _ -> Proof1 DBL (Proof2 APL (compile1 x) (compile1 y))
    _ -> Proof1 DBL (Proof2 APL (compile1 x) (compile1 y))
-}
 compile1 (Proof0 r) = Proof0 r
 compile1 (Proof1 r x) = Proof1 r (compile1 x)
 compile1 (Proof2 r x y) = Proof2 r (compile1 x) (compile1 y)

 compile (Proof0 (FNC f)) = Proof0 (FNC f) 
 compile x = let y = compile1 x in if x == y then y else compile y

 {-
 shift :: Proof -> Proof -> Proof
 shift u (Proof1 DBS x) = if u == Proof1 DBS x then Proof1 DBS u else Proof1 DBS (shift u x)
 shift u (Proof1 DBL x) = Proof1 DBL (shift (Proof1 DBS u) x)
 shift _ (Proof0 r) = Proof0 r
 shift u (Proof1 r x) = Proof1 r (shift u x)
 shift u (Proof2 r x y) = Proof2 r (shift u x) (shift u y)
 -}

 shift :: Proof -> Proof -> Proof
 shift1 :: Proof -> Proof -> Proof
 shift u x = if u == x then Proof1 DBS x else shift1 u x
 shift1 u (Proof1 DBL x) = Proof1 DBL (shift (Proof1 DBS u) x)
 shift1 u (Proof2 LBD v x) = Proof2 LBD v (shift (Proof1 DBS u) x)
 shift1 _ (Proof0 r) = Proof0 r
 shift1 u (Proof1 r x) = Proof1 r (shift u x)
 shift1 u (Proof2 r x y) = Proof2 r (shift u x) (shift u y)

 subst :: Proof -> Proof -> Proof -> Proof
 subst1 :: Proof -> Proof -> Proof -> Proof
 subst u a b = if u == a then b else (if Proof1 DBS u == a then u else subst1 u a b)
 -- subst1 u (Proof1 DBL x) b = Proof1 DBL (subst (Proof1 DBS u) x (shift (Proof0 DB0) b))
 subst1 u (Proof1 DBL x) b = Proof1 DBL (subst (Proof1 DBS u) x (shift u b))
 -- subst1 u (Proof1 DBL x) b = if u == Proof0 DB0 then Proof1 DBL (subst (Proof1 DBS u) x (shift (Proof0 DB0) b)) else Proof1 DBL (subst u x b)
 -- subst1 u (Proof2 LBD v x) b = Proof2 LBD v (subst (Proof1 DBS u) x (shift v b))
 subst1 u (Proof2 LBD v x) b = Proof2 LBD v (subst (Proof1 DBS u) x (shift u b))
 -- subst1 u (Proof2 LBD v x) b = if u == v then Proof2 LBD v (subst (Proof1 DBS u) x (shift u b)) else Proof2 LBD v (subst u x b)
 -- subst1 u (Proof2 LBD v x) b = if cont u v then Proof2 LBD v (subst (Proof1 DBS u) x (shift u b)) else Proof2 LBD v (subst u x b)
 -- subst1 u (Proof1 DBP (Proof1 DBS x)) b = subst1 u x b
 subst1 _ (Proof0 r) _ = Proof0 r
 subst1 u (Proof1 r x) b = Proof1 r (subst u x b)
 subst1 u (Proof2 r x y) b = Proof2 r (subst u x b) (subst u y b)

 red1 :: Proof -> Proof
 red1 (Proof2 APL (Proof0 (FNC f)) y) = f y
 red1 (Proof2 APL (Proof1 DBL x) y) = subst (Proof0 DB0) x y
 red1 (Proof2 APL (Proof2 LBD v x) y) = subst v x y
 -- red1 (Proof2 APL (Proof1 DBL x) y) = subst (Proof0 DB0) (red1 x) (red1 y)
 -- red1 (Proof1 DBS (Proof1 DBP x)) = x
 red1 (Proof1 DBP (Proof1 DBS x)) = x
 -- red1 (Proof1 DBP (Proof1 DBP x)) = Proof1 DBP x
 red1 (Proof1 DBP (Proof1 DBL x)) = Proof1 DBL (Proof1 DBP x)
 -- red1 (Proof1 DBP (Proof2 APL x y)) = Proof2 APL (Proof1 DBP x) (Proof1 DBP y)
 -- red1 (Proof1 DBP (Proof1 r x)) = Proof1 r (Proof1 DBP x)
 -- red1 (Proof1 DBP (Proof2 r x y)) = Proof2 r (Proof1 DBP x) (Proof1 DBP y)
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
 -- LTR : a = b, c = d |- if reduce(a) == reduce(c) then reduce(b) = reduce(d)  
 side s u v (Proof2 LTR x y) =
	if reduce (side LeftSide u v x) == reduce (side LeftSide u v y) 
	then reduce (side RightSide u v (if s == LeftSide then x else y)) 
    else Proof2 LTR x y
 -- LTN : a = b, c = d |- if a or reduce(a) == c or reduce(c) then b = reduce(d)
 side s u v (Proof2 LTN x y) = 
	let lx = side LeftSide u v x
	    ly = side LeftSide u v y
	in let rlx = reduce lx
	       rly = reduce ly
	   in if (lx == ly) || (lx == rly) || (rlx == ly) || (rlx == rly) 
	      -- then reduce (side RightSide u v (if s == LeftSide then x else y))
          then (if s == LeftSide then (side RightSide u v x) else reduce (side RightSide u v y))
	      else Proof2 LTN x y
 -- LT2 : a = b, c = d |- if a or reduce(a) == c or reduce(c) then reduce(b) = reduce(d)
 side s u v (Proof2 LT2 x y) = 
	let lx = side LeftSide u v x
	    ly = side LeftSide u v y
	in let rlx = reduce lx
	       rly = reduce ly
	   in if (lx == ly) || (lx == rly) || (rlx == ly) || (rlx == rly) 
	      then reduce (side RightSide u v (if s == LeftSide then x else y))
          -- then (if s == LeftSide then (side RightSide u v x) else reduce (side RightSide u v y))
	      else Proof2 LT2 x y
 -- LTS : a = b, a = c |- b = c
 side s u v (Proof2 LTS x y) = if (side LeftSide u v x) == (side LeftSide u v y) then (side RightSide u v (if s == LeftSide then x else y)) else Proof2 LTS x y
 -- TRN : a = b, b = c |- a = c
 side s u v (Proof2 TRN x y) = if (side RightSide u v x) == (side LeftSide u v y) then (if s == LeftSide then (side LeftSide u v x) else (side RightSide u v y)) else Proof2 TRN x y
 -- SYM : a = b |- b = a
 side s u v (Proof1 SYM x) = side (if s == LeftSide then RightSide else LeftSide) u v x
 -- SUB : a = b, c = d |- APL (DBL a) c = subst (DB0, b, d)
 side LeftSide u v (Proof2 SUB x y) = Proof2 APL (Proof1 DBL (side LeftSide u v x)) (side LeftSide u v y)
 side RightSide u v (Proof2 SUB x y) = subst (Proof0 DB0) (side RightSide u v x) (side RightSide u v y)
 -- RED : a = b |- a = reduce(b)
 side LeftSide u v (Proof1 RED x) = side LeftSide u v x
 side RightSide u v (Proof1 RED x) = reduce (side RightSide u v x)
 -- RD2 : a = b |- reduce(a) = reduce(b)
 side s u v (Proof1 RD2 x) = reduce (side s u v x)
 -- RDQ : x |- x = reduce(x)
 -- RDQ x = RED (QOT x)
 side LeftSide u v (Proof1 RDQ x) = x
 side RightSide u v (Proof1 RDQ x) = reduce x
 -- ERQ : x |- left(reduce(x)) = right(reduce(x))
 -- ERQ x = EVR (RED (QOT x))
 side s u v (Proof1 ERQ x) = side s u v (reduce x)
 -- LFT : a = b |- a = a
 side _ u v (Proof1 LFT x) = side LeftSide u v x
 -- RGT : a = b |- b = b
 side _ u v (Proof1 RGT x) = side RightSide u v x
 -- QOT : x |- x = x
 side _ _ _ (Proof1 QOT x) = x   
 -- RFE : a = b |- (a = b) = (a = b)
 side s u v (Proof1 RFE x) = equ (side LeftSide u v x) (side RightSide u v x)
 -- EVL : (a = b) = (c = d) |- a = b
 -- EVL (QOT x) = x
 side s u v (Proof1 EVL x) = side s u v (side LeftSide u v x)
 -- EVR : (a = b) = (c = d) |- c = d 
 -- EVR (QOT x) = x
 side s u v (Proof1 EVR x) = side s u v (side RightSide u v x)
 -- NOP : a = b |- a = b
 -- NOP x = x
 side s u v (Proof1 NOP x) = side s u v x
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
 abstr1 d v (Proof2 LBD w x) = Proof2 LBD w (abstr (Proof1 DBS d) v x)
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
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

 reducesTo x = do
  putStr ("\n  " ++ show x ++ "\nreduces to\n  " ++ show (reduce x) ++ "\n")

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
  proves (red (equ (apl (dbl db0) a) (apl (dbl db0) b)))
  proves (rdq (equ (apl (dbl db0) a) (apl (dbl db0) b)))
  proves (red (qot (equ (apl (dbl db0) a) (apl (dbl db0) b))))

  proves (ltr (ltr gpLemma4c gpLemma4c) (ltr gpLemma4c gpLemma3c))
  proves (evr (rdq (apl (apl (dbl (dbl (ltr (ltr (dbs db0) (dbs db0)) (ltr (dbs db0) db0)))) gpLemma4c) gpLemma3c)))
  proves (evr (red (qot (apl (apl (dbl (dbl (ltr (ltr (dbs db0) (dbs db0)) (ltr (dbs db0) db0)))) gpLemma4c) gpLemma3c))))
  proves (evr $ red $ qot $ apl2 ltr2 gpLemma4c gpLemma3c)
  proves (erq (apl2 ltr2 gpLemma4c gpLemma3c))
  proves (lt2 gpLemma4c gpLemma3c)

