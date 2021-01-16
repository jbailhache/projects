module PL where
 
 import Data.List

 data Proof = SMB String
            | VAR 
            | NXV Proof
            | FNC Proof
            | APL Proof Proof
            | LTR Proof Proof
            | EQU Proof Proof			
	deriving (Eq, Show)
	
 data Side = LeftSide | RightSide
	deriving (Eq, Show)

 shift :: Proof -> Proof -> Proof
 shift _ (SMB s) = SMB s
 shift _ VAR = VAR
 shift u (NXV x) = if u == NXV x then NXV u else NXV (shift u x)
 shift u (FNC x) = FNC (shift (NXV u) x)
 shift u (APL x y) = APL (shift u x) (shift u y)
 shift u (LTR x y) = LTR (shift u x) (shift u y)
 shift u (EQU x y) = EQU (shift u x) (shift u y)

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

 red1 :: Proof -> Proof
 red1 (SMB s) = SMB s
 red1 VAR = VAR
 red1 (NXV x) = NXV (red1 x)
 red1 (FNC x) = FNC (red1 x)
 red1 (APL (FNC x) y) = subst VAR x y
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTR x y) = LTR (red1 x) (red1 y)
 red1 (EQU x y) = EQU (red1 x) (red1 y)

 red2 :: [Proof] -> [Proof]
 red2 [] = []
 red2 (x : l) = (red1 x) : (x : l)

 red3 :: [Proof] -> [Proof]
 red3 [] = []
 red3 (x : l) = case find (\y -> cont x y) l of
	Nothing -> red3 (red2 (x : l))
	Just _ -> x : l

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
 
 lambda :: String -> Proof -> Proof
 lambda v x = FNC (abstr VAR v x)


 proves x = do
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

 reducesTo x = do
  putStr ("\n  " ++ show x ++ "\nreduces to\n  " ++ show (red x) ++ "\n")

 ident = FNC VAR

 apl2 f x y = APL (APL f x) y
 apl3 f x y z = APL (APL (APL f x) y) z
 
 -- Application with reduction
 apr r x = LTR (LTR (APL r x) (red (left (APL r x)))) (red (right (APL r x)))
 apr2 r x y = apr (apr r x) y
 apr3 r x y z = apr (apr (apr r x) y) z 


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
					   
 
 test = do
  proves gpTheorem1
