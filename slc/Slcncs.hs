module Slcncs where

 import Data.List
 import Data.Char
 -- import Control.Monad.Cont

 -- strReadFile filename = do
 --  readFile filename >>= \s -> print s

{-
 strReadFile filename = 
  (`runCont` id) $ do
   r <- callCC $ \k -> do
    readFile filename >>= \s -> k s
   return r 
-}

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
  -- show DB0 = "DB0"
  show DB0 = "*"
  show (SMB s) = s

 instance Show Rule1 where
  -- show DBS = "+"
  show DBS = "'"
  -- show DBP = "P"
  show DBP = "DBP "
  show NXT = "*"
  show DBL = "\\"
  show SYM = "SYM "
  show RED = "RED "
  show RD2 = "RD2 "
  show RDQ = "RDQ "
  show ERQ = "ERQ "
  show LFT = "LFT "
  show RGT = "RGT "
  show QOT = "QOT "
  show RFE = "RFE "
  show EVL = "EVL "
  show EVR = "EVR "
  show NOP = "NOP "

 instance Show Rule2 where
  show EQU = "="
  show APL = "-"
  -- show LTR = "&"
  show LTR = "LTR"
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


 apply (Proof1 DBL (Proof0 DB0)) y = y
 apply x y = apl x y


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


 showapl (Proof2 APL x y) (Proof2 APL z t) = showapl x y ++ " : " ++ showapl z t
 showapl (Proof2 APL x y) z = showapl x y ++ " " ++ show z
 showapl x (Proof2 APL y z) = show x ++ " : " ++ showapl y z
 showapl x y = show x ++ " " ++ show y

 showproof (Proof0 (SMB s)) = s
 showproof (Proof1 DBL (Proof2 APL x y)) = "[" ++ showapl x y ++ "]"
 showproof (Proof1 DBL x) = "[" ++ showproof x ++ "]"
 showproof (Proof2 APL x y) = "(" ++ showapl x y ++ ")"
 showproof (Proof0 r) = show r
 showproof (Proof1 r x) = show r ++ showproof x
 -- showproof (Proof1 r x) = show r ++ " " ++ showproof x
 showproof (Proof2 r x y) = show r ++ " " ++ showproof x ++ " " ++ showproof y

 instance Show Proof where
  -- show x = showlevel 1 0 x
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


{-
 print_proof n = do
  putStrLn $ show $ nthproof n 

 print_proofs n p = do
  if n > p then return else do
   print_proof n
   print_proofs (n+1) p
   return
-}

{-
 split1 d w [] = [w]
 split1 d w (x : s) = if elem x d then (if w == [] then split1 d [] s else w : split1 d [] s) else split1 d (w ++ [x]) s

 split d s = split1 d [] s
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


{-
 slc "" = (smb "?", "")
 slc (' ' : s) = slc s
 slc ('#' : s) = (axm, s)
 slc ('$' : s) = (db0, s)
 slc ('+' : s) = let (x, t) = slc s in (dbs x, t)
 slc ('\'' : s) = let (x, t) = slc s in (dbs x, t)
 slc ('\\' : s) = let (x, t) = slc s in (dbl x, t)
 slc ('/' : s) = let (x, t) = slc s in (dbl x, t)
 slc ('L' : c : s) = let (x, t) = slc s in let (y, u) = slc t in (apl (lambda (c : "") y) x, u)
 slc ('-' : s) = let (x, t) = slc s in let (y, u) = slc t in (apl x y, u)
 slc ('&' : s) = let (x, t) = slc s in let (y, u) = slc t in (ltr x y, u)
 slc ('^' : c : s) = let (x, t) = slc s in (lambda (c : "") x, t)
 slc (c : s) = (smb (c : ""), s)
-}

{-
 slc1 ("AXM" : s) = (axm, s)
 slc1 ("DB0" : s) = (db0, s)
 slc1 ("$"   : s) = (db0, s)
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
 slc1 (":"   : v : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (apl (lambda v y) x, u)
 slc1 ("LBD" : v : s) = let (x, t) = slc1 s in (lambda v x, t)
 slc1 ("^"   : v : s) = let (x, t) = slc1 s in (lambda v x, t)
 slc1 (w : s) = (smb w, s)
-}

 -- slc s = let (x, t) = slc1 (split " " s) in if t == [] then Just x else Nothing
 -- slc s = let (x, t) = slc1 (split " \t\n" s) in if t == [] || head t == "" then x else smb ("Error : Unexpected '" ++ concat (map (\x -> x ++ " ") t) ++ "'")



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

 slc1 ("DBP" : s) e = let (x, t) = slc1 s e in (dbp x, t)
 slc1 ("NXT" : s) e = let (x, t) = slc1 s e in (nxt x, t)
 slc1 ("SYM" : s) e = let (x, t) = slc1 s e in (sym x, t)
 slc1 ("RED" : s) e = let (x, t) = slc1 s e in (red x, t)
 slc1 ("RD2" : s) e = let (x, t) = slc1 s e in (rd2 x, t)
 slc1 ("ERQ" : s) e = let (x, t) = slc1 s e in (erq x, t)
 slc1 ("LFT" : s) e = let (x, t) = slc1 s e in (lft x, t)
 slc1 ("RGT" : s) e = let (x, t) = slc1 s e in (rgt x, t)
 slc1 ("QOT" : s) e = let (x, t) = slc1 s e in (qot x, t)
 slc1 ("RFE" : s) e = let (x, t) = slc1 s e in (rfe x, t)
 slc1 ("EVL" : s) e = let (x, t) = slc1 s e in (evl x, t)
 slc1 ("EVR" : s) e = let (x, t) = slc1 s e in (evr x, t)
 slc1 ("NOP" : s) e = let (x, t) = slc1 s e in (nop x, t)

 slc1 ("LTN" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (ltn x y, u)
 slc1 ("LT2" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (lt2 x y, u)
 slc1 ("LTS" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (lts x y, u)
 slc1 ("TRN" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (trn x y, u)
 slc1 ("SUB" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (sub x y, u)
 slc1 ("LBD" : s) e = let (x, t) = slc1 s e in let (y, u) = slc1 t e in (lbd x y, u) 

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

{-
 slc2 s e x c = 
  case s of
   e : t -> case c of
    False -> (x, t)
    True -> (x, s)
   _ -> case x of
    Proof1 DBL (Proof0 DB0) -> let (y, t) = slc1 s e in slc2 t e y c
    _ -> let (y, t) = slc1 s e in slc2 t e (apl x y) c
-}


{-
 slc2 (")" : s) x False = (x, s)
 slc2 (")" : s) x True = (x, ")" : s)
 slc2 s (Proof1 DBL (Proof0 DB0)) c = let (y, t) = slc1 s in slc2 t y c
 slc2 s x c = let (y, t) = slc1 s in slc2 t (apl x y) c

 slc3 ("]" : s) x = (x, s)
 slc3 s (Proof1 DBL (Proof0 DB0))  = let (y, t) = slc1 s in slc3 t y 
 slc3 s x = let (y, t) = slc1 s in slc3 t (apl x y) 
-}

 -- slc s = let (x, t) = slc1 (split " " s) in if t == [] then Just x else Nothing

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
  proves (red (equ (apl (dbl db0) a) (apl (dbl db0) b)))
  proves (rdq (equ (apl (dbl db0) a) (apl (dbl db0) b)))
  proves (red (qot (equ (apl (dbl db0) a) (apl (dbl db0) b))))

  proves (ltr (ltr gpLemma4c gpLemma4c) (ltr gpLemma4c gpLemma3c))
  proves (evr (rdq (apl (apl (dbl (dbl (ltr (ltr (dbs db0) (dbs db0)) (ltr (dbs db0) db0)))) gpLemma4c) gpLemma3c)))
  proves (evr (red (qot (apl (apl (dbl (dbl (ltr (ltr (dbs db0) (dbs db0)) (ltr (dbs db0) db0)))) gpLemma4c) gpLemma3c))))
  proves (evr $ red $ qot $ apl2 ltr2 gpLemma4c gpLemma3c)
  proves (erq (apl2 ltr2 gpLemma4c gpLemma3c))
  proves (lt2 gpLemma4c gpLemma3c)

