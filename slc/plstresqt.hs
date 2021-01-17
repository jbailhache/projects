module PL where
 
 import Data.List

 data Proof = SMB String
            | VAR 
            | NXV Proof
            | FNC Proof
            | APL Proof Proof
            | LTR Proof Proof
            | EQU Proof Proof	
			| ESQ Proof
	deriving (Eq)
	
 data Side = LeftSide | RightSide
	deriving (Eq, Show)

 data Context = Function | Argument | Other
	deriving (Eq, Show)


 -- shift u x increases all variables greater than u in x
 shift :: Proof -> Proof -> Proof
 shift _ (SMB s) = SMB s
 shift VAR VAR = NXV VAR
 shift _ VAR = VAR
 shift (NXV u) (NXV x) = NXV (shift u x)
 shift u (NXV x) = NXV (shift u x)
 shift u (FNC x) = FNC (shift (NXV u) x)
 shift u (APL x y) = APL (shift u x) (shift u y)
 shift u (LTR x y) = LTR (shift u x) (shift u y)
 shift u (EQU x y) = EQU (shift u x) (shift u y)
 shift u (ESQ x) = ESQ (shift u x)
 
 -- subst u a b (approximatively) replaces u in a by b (a little more complex in fact)
 subst :: Proof -> Proof -> Proof -> Proof
 subst1 :: Proof -> Proof -> Proof -> Proof
 subst u a b = if u == a then b else (if NXV u == a then u else subst1 u a b)
 subst1 _ (SMB s) _ = SMB s
 subst1 _ VAR _ = VAR
 subst1 u (NXV x) b = NXV (subst u x b)
 subst1 u (FNC x) b = FNC (subst (NXV u) x (shift VAR b))
 subst1 u (APL x y) b = APL (subst u x b) (subst u y b)
 subst1 u (LTR x y) b = LTR (subst u x b) (subst u y b)
 subst1 u (EQU x y) b = EQU (subst u x b) (subst u y b)
 subst1 u (ESQ x) b = ESQ (subst u x b)
 
 -- cont x y tests if x contains y 
 cont :: Proof -> Proof -> Bool
 cont1 :: Proof -> Proof -> Bool
 cont x y = if x == y then True else cont1 x y
 cont1 (SMB s) _ = False
 cont1 VAR _ = False
 cont1 (NXV x) y = cont x y
 cont1 (FNC x) y = cont x y
 cont1 (APL x y) z = (cont x z) || (cont y z)
 cont1 (LTR x y) z = (cont x z) || (cont y z)
 cont1 (EQU x y) z = (cont x z) || (cont y z)
 cont1 (ESQ x) y = cont x y
 
 -- red1 does one step of reduction
 red1 :: Proof -> Proof
 red1 (SMB s) = SMB s
 red1 VAR = VAR
 red1 (NXV x) = NXV (red1 x)
 red1 (FNC x) = FNC (red1 x)
 red1 (APL (FNC x) y) = subst VAR x y
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTR x y) = LTR (red1 x) (red1 y)
 red1 (EQU x y) = EQU (red1 x) (red1 y)
 red1 (ESQ x) = ESQ (red1 x)
 
 red2 :: [Proof] -> [Proof]
 red2 [] = []
 red2 (x : l) = (red1 x) : (x : l)

 red3 :: [Proof] -> [Proof]
 red3 [] = []
 red3 (x : l) = case find (\y -> cont x y) l of
	Nothing -> red3 (red2 (x : l))
	Just _ -> x : l

 -- red : reduction
 red :: Proof -> Proof
 red x = case red3 (x : []) of
		[] -> x
		y : m -> y

 side :: Side -> Proof -> Proof
 side _ (SMB s) = SMB s
 side _ VAR = VAR
 side s (NXV x) = NXV (side s x)
 side s (FNC x) = FNC (side s x)
 side s (APL x y) = APL (side s x) (side s y)
 side s (LTR x y) = if red (side LeftSide x) == red (side LeftSide y) then (side RightSide (if s == LeftSide then x else y)) else LTR x y
 side LeftSide (EQU x y) = x
 side RightSide (EQU x y) = y
 side s (ESQ x) = side s (red1 x)
 
 left = side LeftSide 
 right = side RightSide 


 contSmb :: Proof -> String -> Bool
 contSmb x s = cont x (SMB s)
 
 abstr :: Proof -> String -> Proof -> Proof
 abstr1 :: Proof -> String -> Proof -> Proof
 abstr d v x = if (contSmb x v) then (abstr1 d v x) else x
 abstr1 d v (EQU x y) = EQU (abstr d v x) (abstr d v y)
 abstr1 d v (SMB s) = if v == s then d else (SMB s)
 abstr1 d v VAR = VAR
 abstr1 d v (NXV x) = NXV (abstr d v x)
 abstr1 d v (FNC x) = FNC (abstr (NXV d) v x)
 abstr1 d v (APL x y) = APL (abstr d v x) (abstr d v y)
 abstr1 d v (LTR x y) = LTR (abstr d v x) (abstr d v y)
 abstr1 d v (ESQ x) = ESQ (abstr1 d v x)
 
 lambda :: String -> Proof -> Proof
 lambda v x = FNC (abstr VAR v x)


 proves x = do
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

 reducesTo x = do
  putStr ("\n  " ++ show x ++ "\nreduces to\n  " ++ show (red x) ++ "\n")

 ident = FNC VAR

 -- Multiple application
 apl2 f x y = APL (APL f x) y
 apl3 f x y z = APL (APL (APL f x) y) z
 
 -- Application with reduction
 apr r x = LTR (LTR (APL r x) (red (left (APL r x)))) (red (right (APL r x)))
 apr2 r x y = apr (apr r x) y
 apr3 r x y z = apr (apr (apr r x) y) z 
					   
 column col s = let l = length (lines s) in if l > 1 then length $ last $ lines s else col + length s 
 
 -- showproof1 ctx col x : user readable representation of x in context ctx at column col
 showproof1 :: Context -> Int -> Proof -> String
 showproof1 _ _ (SMB s) = s
 showproof1 _ _ VAR = "*"
 showproof1 _ col (NXV x) = "'" ++ showproof1 Other (col+1) x
 showproof1 _ col (FNC x) = "[" ++ showproof1 Other (col+1) x ++ "]"
 showproof1 Argument col (APL x y) = "(" ++ showproof1 Other (col+1) (APL x y) ++ ")"
 showproof1 _ col (APL x y) = let s = showproof1 Function col x in s ++ " " ++ showproof1 Argument (column col s + 1) y 
 -- showproof1 _ (LTR x y) = "{ " ++ showproof1 Other x ++ " , " ++ showproof1 Other y ++ " }"
 showproof1 _ col (LTR x y) = "{ " ++ showproof1 Other (col+2) x ++ " ,\n" ++ concat (replicate (col+2) " ") ++ showproof1 Other (col+2) y ++ " }"
 -- showproof1 Other col (EQU x y) = let s = showproof1 Other col x in s ++ " = " ++ showproof1 Other (col + (length s) + 3) y 
 -- showproof1 _ col (EQU x y) = "(" ++ showproof1 Other (col+1) (EQU x y) ++ ")"
 showproof1 _ col (EQU x y) = let s = showproof1 Other col x in "(" ++ s ++ " = " ++ showproof1 Other (column col s + 4) y ++ ")" 
 showproof1 _ col (ESQ x) = "@" ++ showproof1 Other (col+1) x
 
 -- showproof2 c m x = (lines (showproof1 c x)) !! 0 ++ "\n" ++ concat (map (\ line -> concat (replicate m "    ") ++ line ++ "\n") (drop 1 (lines (showproof1 c x))))
 
 -- showproof x = user readable representation of proof x
 showproof = showproof1 Other 0
 
 instance Show Proof where
  show x = showproof x
 
 -- substitute x by y in z
 substitute x y z = if x == z then y else substitute1 x y z
 substitute1 x y (SMB s) = SMB s
 substitute1 x y VAR = VAR
 substitute1 x y (NXV z) = NXV (substitute x y z)
 substitute1 x y (FNC z) = FNC (substitute x y z)
 substitute1 x y (APL z t) = APL (substitute x y z) (substitute x y t)
 substitute1 x y (LTR z t) = LTR (substitute x y z) (substitute x y t)
 substitute1 x y (EQU z t) = EQU (substitute x y z) (substitute x y t)
 substitute1 x y (ESQ z) = ESQ (substitute x y z)
 
 pl1 (' ' : s) = pl1 s
 pl1 ('\t' : s) = pl1 s
 pl1 ('\n' : s) = pl1 s
 pl1 ('(' : s) = pl3 ')' Nothing Nothing s
 -- pl1 (':' : s) = let (x, t) = pl3 ')' Nothing (FNC VAR) s in (x, (')' : t))
 pl1 ('*' : s) = (VAR, s)
 pl1 ('\'' : s) = let (x, t) = pl1 s in (NXV x, t)
 pl1 ('\\' : s) = let (x, t) = pl1 s in (FNC x, t)
 pl1 ('[' : s) = let (x, t) = pl3 ']' Nothing Nothing s in (FNC x, t)
 pl1 ('-' : s) = let (x, t) = pl1 s in let (y, u) = pl1 t in (apr x y, u)
 pl1 ('%' : s) = let (x, t) = pl1 s in let (y, u) = pl1 t in (LTR x y, u)
 pl1 ('{' : s) = let (x, t) = pl3 ',' Nothing Nothing s in let (y, u) = pl3 '}' Nothing Nothing t in (LTR x y, u)
 pl1 ('#' : s) = let (x, t) = pl1 s in let (y, u) = pl1 t in (EQU x y, u)
 pl1 ('@' : s) = let (x, t) = pl1 s in (ESQ x, t)
 pl1 ('^' : s) = let (x, t) = pl1 s in case x of SMB v -> let (y, u) = pl1 t in (lambda v y, u)
 -- pl1 ('!' : s) = let (x, t) = pl1 s in case x of SMB v -> let (y, u) = pl1 t in let (z, w) = pl1 u in (apr (lambda v z) y, w)
 -- pl1 ('!' : s) = let (x, t) = pl1 s in let (y, u) = pl1 t in let (z, v) = pl1 u in (substitute x y z, v)
 pl1 ('!' : s) = let (x, t) = pl1 s in case x of SMB x1 -> let (y, u) = pl1 t in let (z, v) = pl1 u in (ESQ (APL (lambda x1 z) y), v)
 -- pl1 ('!' : s) = let (x, t) = pl1 s in case x of SMB x1 -> let (y, u) = pl1 t in let (z, v) = pl1 u in (APL (lambda x1 z) y, v)
 pl1 ('$' : s) = let (x, t) = pl1 s in (red x, t)
 pl1 ('<' : s) = let (x, t) = pl1 s in (left x, t)
 pl1 ('>' : s) = let (x, t) = pl1 s in (right x, t)
 pl1 (c : s) = pl4 [c] s
 
 pl4 s "" = (SMB s, "")
 pl4 s (' ' : t) = (SMB s, t)
 pl4 s ('\t' : t) = (SMB s, t)
 pl4 s ('\n' : t) = (SMB s, t)
 pl4 s (c : t) = if (any.(==)) c " \t\n()*'\\[]-%{,}#=" then (SMB s, (c : t)) else pl4 (s ++ [c]) t
 
 pl2 e (' ' : s) = pl2 e s
 pl2 e ('\t' : s) = pl2 e s
 pl2 e ('\n' : s) = pl2 e s
 pl2 e "" = (False, Nothing, "")
 -- pl2 ':' ('=' : s) 
 -- pl2 ':' (c : s) = if (any.(==)) c ")]}=" then 
 pl2 e (c : s) = if c == e then (False, Nothing, s) else if c == '=' then (True, Nothing, s) else let (x, t) = pl1 (c : s) in (False, Just x, t)
 
 pl3 e l Nothing (':' : s) = let (y, t) = pl3 e l Nothing s in (y, t)
 pl3 e l (Just x) (':' : s) = let (y, t) = pl3 e l Nothing s in (APL x y, t)
 pl3 e l x1 s = let x = case x1 of { Nothing -> FNC VAR; Just x2 -> x2 } in case pl2 e s of
	(False, Nothing, t) -> case l of 
	                           Nothing -> (x, t)
	                           Just l -> (EQU l x, t)
	(True, Nothing, t) -> case l of 
	                          Nothing -> pl3 e (Just x) Nothing t
	                          Just l -> pl3 e (Just (EQU l x)) Nothing t		
	(False, Just y, t) -> case x1 of 
	                          Nothing -> pl3 e l (Just y) t
	                          _ -> pl3 e l (Just (APL x y)) t
		 
 pl s = let (x, t) = pl3 '.' Nothing Nothing s in x
 
 
 run filename = do
  -- readFile filename >>= \s -> proves $ slc s
  -- readFile filename >>= \s -> proves (let x = slc s in ltr x x)
  -- readFile filename >>= \s -> proves $ reduce $ slc s
  readFile filename >>= \s -> proves $ pl s 				
				
 -- Example of theory
 
 parent = apl2 (SMB "parent")
 grandparent = apl2 (SMB "grandparent")
 allan = SMB "allan"
 brenda = SMB "brenda"
 charles = SMB "charles"

 gpRule1 = lambda "x" $ lambda "y" $ lambda "z" $ 
  EQU (APL (parent (SMB "x") (SMB "y")) $
       APL (parent (SMB "y") (SMB "z")) $
       grandparent (SMB "x") (SMB "z"))
      ident
 gpAxiom1 = EQU (parent allan brenda) ident
 gpAxiom2 = EQU (parent brenda charles) ident
 
 gpTheorem1 = LTR (apr gpAxiom2 (grandparent allan charles))
                  (LTR (apr gpAxiom1 (apr (parent brenda charles) (grandparent allan charles)))
                       (apr3 gpRule1 allan brenda charles))

				
 gpRule1b = pl "^x ^y ^z ( (parent x y : parent y z : grandparent x z) = [*] )"
 gpAxiom1b = pl "parent allan brenda = [*]"
 gpAxiom2b = pl "parent brenda charles = [*]"
 
 gpTheorem1b = LTR (apr gpAxiom2b (grandparent allan charles))
                   (LTR (apr gpAxiom1b (apr (parent brenda charles) (grandparent allan charles)))
                        (apr3 gpRule1b allan brenda charles))
								
 -- does not work					
 gpTheorem1c = pl "\
  \ ! gpRule1  ^x ^y ^z ( (parent x y : parent y z : grandparent x z) = [*] ) \
  \ ! gpAxiom1 (parent allan brenda = [*]) \
  \ ! gpAxiom2 (parent brenda charles = [*]) \
  \ ! gpTheorem1 { - gpAxiom1 (grandparent allan charles) , \
  \                { - gpAxiom1 - (parent brenda charles) (grandparent allan charles) , \
  \                  --- gpRule1 allan brenda charles } } \
  \ gpTheorem1 "
  
 gptest1 = pl "\
  \ ! gpRule1  ^x ^y ^z ( (parent x y : parent y z : grandparent x z) = [*] ) \
  \ ! gpAxiom1 (parent allan brenda = [*]) \
  \ ! gpAxiom2 (parent brenda charles = [*]) \
  \ ! gpTheorem1 { - gpAxiom1 (grandparent allan charles) , \
  \                { - gpAxiom1 - (parent brenda charles) (grandparent allan charles) , \
  \                  --- gpRule1 allan brenda charles } } \
  \ --- gpRule1 allan brenda charles "

 gptest2 = pl "\
  \ ! gpRule1  ^x ^y ^z ( (parent x y : parent y z : grandparent x z) = [*] ) \
  \ --- gpRule1 allan brenda charles "
 
 test1 = pl "\
  \ ! gpRule1  ^x ^y ^z ( (parent x y : parent y z : grandparent x z) = [*] ) \
  \ ! gpAxiom1 (parent allan brenda = [*]) \
  \ ! gpAxiom2 (parent brenda charles = [*]) \
  \ gpRule1 "
  
 gpTheorem1d = pl "\
  \ ! gpRule1  ^x ^y ^z ( (parent x y : parent y z : grandparent x z) = [*] ) \
  \ ! gpAxiom1 (parent allan brenda = [*]) \
  \ ! gpAxiom2 (parent brenda charles = [*]) \
  \ ! gpLemma1d (gpRule1 allan brenda charles) \
  \ ! gpLemma2d (gpAxiom1 (parent brenda charles (grandparent allan charles))) \
  \ ! gpLemma3d1 { gpLemma2d , gpLemma1d } \
  \ ! gpLemma3d { { gpLemma3d1 , (parent brenda charles (grandparent allan charles)) } , [*] } \
  \ ! gpLemma4d (gpAxiom2 (grandparent allan charles)) \
  \ ! gpLemma5d { gpLemma4d , gpLemma3d } \
  \ ! gpTheorem1d { grandparent allan charles , gpLemma5d } \
  \ gpTheorem1d "
  
 testRule1 = pl "^x (x x = x)"
 testTheorem1 = pl "! testRule1 ^x (x x = x) { { testRule1 a , $ < (testRule1 a) } , $ > (testRule1 a) }"
 testTheorem1b = pl " { { ^x(x x=x) a , $ < (^x(x x=x) a) } , $ > (^x(x x=x) a) } "
 testTheorem1c = pl "{ { testRule1 a , $ < (testRule1 a) } , $ > (testRule1 a) }"
 
-- inc = do
--  let counter = 0
--  counter1 <- counter + 1
--  putStrLn (show counter1)
		
 test = do
  proves gpTheorem1
