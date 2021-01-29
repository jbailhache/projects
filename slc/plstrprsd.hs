module PL where
 
 import Data.List
 
 data Proof = SMB String
            | VAR 
            | NXV Proof
            | FNC Proof
            | RED Proof
            | APL Proof Proof
            | LTR Proof Proof
			| RTR Proof Proof
            | EQU Proof Proof			
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
 shift u (RED x) = RED (shift u x)
 shift u (APL x y) = APL (shift u x) (shift u y)
 shift u (LTR x y) = LTR (shift u x) (shift u y)
 shift u (RTR x y) = RTR (shift u x) (shift u y)
 shift u (EQU x y) = EQU (shift u x) (shift u y)

 -- subst u a b (approximatively) replaces u in a by b (a little more complex in fact)
 subst :: Proof -> Proof -> Proof -> Proof
 subst1 :: Proof -> Proof -> Proof -> Proof
 subst u a b = if u == a then b else (if NXV u == a then u else subst1 u a b)
 subst1 _ (SMB s) _ = SMB s
 subst1 _ VAR _ = VAR
 subst1 u (NXV x) b = NXV (subst u x b)
 subst1 u (FNC x) b = FNC (subst (NXV u) x (shift VAR b))
 subst1 u (RED x) b = RED (subst u x b)
 subst1 u (APL x y) b = APL (subst u x b) (subst u y b)
 subst1 u (LTR x y) b = LTR (subst u x b) (subst u y b)
 subst1 u (RTR x y) b = RTR (subst u x b) (subst u y b) 
 subst1 u (EQU x y) b = EQU (subst u x b) (subst u y b)

 -- cont x y tests if x contains y 
 cont :: Proof -> Proof -> Bool
 cont1 :: Proof -> Proof -> Bool
 cont x y = if x == y then True else cont1 x y
 cont1 (SMB s) _ = False
 cont1 VAR _ = False
 cont1 (NXV x) y = cont x y
 cont1 (FNC x) y = cont x y
 cont1 (RED x) y = cont x y
 cont1 (APL x y) z = (cont x z) || (cont y z)
 cont1 (LTR x y) z = (cont x z) || (cont y z)
 cont1 (RTR x y) z = (cont x z) || (cont y z)
 cont1 (EQU x y) z = (cont x z) || (cont y z)

 -- red1 does one step of reduction
 red1 :: Proof -> Proof
 red1 (SMB s) = SMB s
 red1 VAR = VAR
 red1 (NXV x) = NXV (red1 x)
 red1 (FNC x) = FNC (red1 x)
 red1 (RED x) = RED (red1 x)
 red1 (APL (FNC x) y) = subst VAR x y
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTR x y) = LTR (red1 x) (red1 y)
 red1 (RTR x y) = RTR (red1 x) (red1 y) 
 red1 (EQU x y) = EQU (red1 x) (red1 y)

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
 side s (RED x) = side s (red x)
 side s (APL x y) = APL (side s x) (side s y)
 side s (LTR x y) = if red (side LeftSide x) == red (side LeftSide y) then (side RightSide (if s == LeftSide then x else y)) else LTR x y
 side s (RTR x y) = if red (side RightSide x) == red (side RightSide y) then (side LeftSide (if s == LeftSide then x else y)) else RTR x y
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
 abstr1 d v (RED x) = RED (abstr d v x)
 abstr1 d v (APL x y) = APL (abstr d v x) (abstr d v y)
 abstr1 d v (LTR x y) = LTR (abstr d v x) (abstr d v y)
 abstr1 d v (RTR x y) = RTR (abstr d v x) (abstr d v y)
 
 lambda :: String -> Proof -> Proof
 lambda v x = FNC (abstr VAR v x)


 proves x = do
  putStr ("\nThe proof\n  " ++ showproof1 Other 2 x ++ " \nproves\n  " ++ showproof1 Other 2 (left x) ++ "\n= " ++ showproof1 Other 2 (right x) ++ "\n")

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
 showproof1 _ col (NXV x) = "'" ++ showproof1 Argument (col+1) x
 showproof1 _ col (FNC x) = "[" ++ showproof1 Other (col+1) x ++ "]"
 showproof1 _ col (RED x) = "@" ++ showproof1 Argument (col+1) x
 showproof1 Argument col (APL x y) = "(" ++ showproof1 Other (col+1) (APL x y) ++ ")"
 showproof1 _ col (APL x y) = let s = showproof1 Function col x in s ++ " " ++ showproof1 Argument (column col s + 1) y 
 -- showproof1 _ (LTR x y) = "{ " ++ showproof1 Other x ++ " , " ++ showproof1 Other y ++ " }"
 showproof1 _ col (LTR x y) = "{ " ++ showproof1 Other (col+2) x ++ " ,\n" ++ concat (replicate (col+2) " ") ++ showproof1 Other (col+2) y ++ " }"
 showproof1 _ col (RTR x y) = "< " ++ showproof1 Other (col+2) x ++ " |\n" ++ concat (replicate (col+2) " ") ++ showproof1 Other (col+2) y ++ " >"
 -- showproof1 Other col (EQU x y) = let s = showproof1 Other col x in s ++ " = " ++ showproof1 Other (col + (length s) + 3) y 
 -- showproof1 _ col (EQU x y) = "(" ++ showproof1 Other (col+1) (EQU x y) ++ ")"
 showproof1 _ col (EQU x y) = let s = showproof1 Other (col+1) x in "(" ++ s ++ " = " ++ showproof1 Other (column (col+1) s + 3) y ++ ")" 
  
 -- showproof x = user readable representation of proof x
 showproof = showproof1 Other 0
 
 instance Show Proof where
  show x = showproof x
 

 -- Convert string to proof
 
 pl1 (' ' : s) = pl1 s
 pl1 ('\t' : s) = pl1 s
 pl1 ('\n' : s) = pl1 s
 pl1 ('\r' : s) = pl1 s
 pl1 ('#' : s) = pl1 $ concat $ map (\l -> l ++ "\n") $ tail $ lines s
 pl1 ('(' : s) = pl3 ')' Nothing Nothing s
 pl1 ('*' : s) = (VAR, s)
 pl1 ('\'' : s) = let (x, t) = pl1 s in (NXV x, t)
 pl1 ('[' : s) = let (x, t) = pl3 ']' Nothing Nothing s in (FNC x, t)
 pl1 ('@' : s) = let (x, t) = pl1 s in (RED x, t)
 pl1 ('-' : s) = let (x, t) = pl1 s in let (y, u) = pl1 t in (apr x y, u)
 pl1 ('{' : s) = let (x, t) = pl3 ',' Nothing Nothing s in let (y, u) = pl3 '}' Nothing Nothing t in (LTR x y, u)
 pl1 ('<' : s) = let (x, t) = pl3 '|' Nothing Nothing s in let (y, u) = pl3 '>' Nothing Nothing t in (RTR x y, u)
 pl1 ('^' : s) = let (x, t) = pl1 s in case x of SMB v -> let (y, u) = pl1 t in (lambda v y, u)
 pl1 ('!' : s) = let (x, t) = pl1 s in case x of SMB x1 -> let (y, u) = pl1 t in let (z, v) = pl1 u in (RED (APL (lambda x1 z) y), v)
 pl1 (c : s) = pl4 [c] s
 
 pl4 s "" = (SMB s, "")
 pl4 s (' ' : t) = (SMB s, t)
 pl4 s ('\t' : t) = (SMB s, t)
 pl4 s ('\n' : t) = (SMB s, t)
 pl4 s ('\r' : t) = (SMB s, t)
 pl4 s (c : t) = if (any.(==)) c " \t\n()*'\\[]-%{,}<|>#=" then (SMB s, (c : t)) else pl4 (s ++ [c]) t
 
 pl2 e (' ' : s) = pl2 e s
 pl2 e ('\t' : s) = pl2 e s
 pl2 e ('\n' : s) = pl2 e s
 pl2 e ('\r' : s) = pl2 e s
 pl2 e "" = (False, Nothing, "")
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
                  (LTR (apr gpAxiom1 (APL (parent brenda charles) (grandparent allan charles)))
                       (apr3 gpRule1 allan brenda charles))

				
 gpRule1b = pl "^x ^y ^z ( (parent x y : parent y z : grandparent x z) = [*] )"
 gpAxiom1b = pl "parent allan brenda = [*]"
 gpAxiom2b = pl "parent brenda charles = [*]"
 
 gpTheorem1b = LTR (apr gpAxiom2b (grandparent allan charles))
                   (LTR (apr gpAxiom1b (APL (parent brenda charles) (grandparent allan charles)))
                        (apr3 gpRule1b allan brenda charles))
								  
 gpTheorem1c = pl "\
  \ ! gpRule1  ^x ^y ^z ( (parent x y : parent y z : grandparent x z) = [*] ) \
  \ ! gpAxiom1 (parent allan brenda = [*]) \
  \ ! gpAxiom2 (parent brenda charles = [*]) \
  \ ! gpLemma1c (gpRule1 allan brenda charles) \
  \ ! gpLemma2c (gpAxiom1 (parent brenda charles (grandparent allan charles))) \
  \ ! gpLemma3c1 { gpLemma2c , gpLemma1c } \
  \ ! gpLemma3c { { gpLemma3c1 , (parent brenda charles (grandparent allan charles)) } , [*] } \
  \ ! gpLemma4c (gpAxiom2 (grandparent allan charles)) \
  \ ! gpLemma5c { gpLemma4c , gpLemma3c } \
  \ ! gpTheorem1c { grandparent allan charles , gpLemma5c } \
  \ gpTheorem1c "

 test = do
  proves gpTheorem1
  proves gpTheorem1b
  proves gpTheorem1c
  
 sizeproof (SMB _) = 1
 sizeproof VAR = 1
 sizeproof (NXV x) = 1 + sizeproof x
 sizeproof (FNC x) = 1 + sizeproof x
 sizeproof (RED x) = 1 + sizeproof x
 sizeproof (APL x y) = 1 + sizeproof x + sizeproof y
 sizeproof (LTR x y) = 1 + sizeproof x + sizeproof y
 sizeproof (RTR x y) = 1 + sizeproof x + sizeproof y
 sizeproof (EQU x y) = 1 + sizeproof x + sizeproof y
 
 value x = 2 * sizeproof x / (sizeproof (left x) + sizeproof (right x))
 
 axioms = [
	VAR,
	SMB "parent",
	SMB "grandparent",
	SMB "allan",
	SMB "brenda",
	SMB "charles",
	gpRule1,
	gpAxiom1,
	gpAxiom2
	]
 
 data ValuedProof = ValuedProof Proof Float deriving (Eq, Show)
 
 give_value x = ValuedProof x (value x)
 
 give_values = map give_value
 
 sort_proofs = sortBy (\xv -> case xv of ValuedProof x vx -> \yv -> case yv of ValuedProof y vy -> compare vy vx)
 
 used v = v * 0.5
 
 data BestAndOther = BestAndOther Proof [ValuedProof]
 
 deduce1 lvp =
   let slvp = sort_proofs lvp in 
   let xv = head slvp in case xv of 
    ValuedProof x vx -> 
     let yv = head (tail slvp) in case yv of 
      ValuedProof y vy -> 
        give_value (NXV x) :
        give_value (NXV y) :
        give_value (FNC x) :
        give_value (FNC y) :
        give_value (APL x y) : 
        give_value (APL y x) :
        give_value (LTR x y) :
        give_value (LTR y x) :
        ValuedProof x (used vx) :
        ValuedProof y (used vy) :
        tail (tail slvp)  
  
 best_of lvp = 
  let bv = foldr1 (\xv -> case xv of ValuedProof x vx -> \yv -> case yv of ValuedProof y vy -> if value x >= value y then xv else yv) lvp in
   case bv of
    ValuedProof b vb -> b

 biggest_of lvp = 
  let bv = foldr1 (\xv -> case xv of ValuedProof x vx -> \yv -> case yv of ValuedProof y vy -> if sizeproof x >= sizeproof y then xv else yv) lvp in
   case bv of
    ValuedProof b vb -> b
 
 deduce bao =
  case bao of
   BestAndOther best lvp ->
    let nlvp = deduce1 lvp in
	 let nbest = best_of nlvp in
	  if value nbest > value best then BestAndOther nbest nlvp else BestAndOther best nlvp
	 
 print_deductions bao target = do
  case bao of 
   BestAndOther best lvp ->
    if value best >= target 
	 then return()
	 else do
	  let nbao = deduce bao in
	   case nbao of
	    BestAndOther nbest nlvp ->
		 let biggest = biggest_of nlvp in
		 if nbest == best 
		  then do
		   putStr ("\n" ++ show (length nlvp) ++ " proofs")
		   putStr ("\nSize of biggest proof is " ++ show (sizeproof biggest))
		   proves biggest
		   putStr ("\nBest proof with value " ++ show (value nbest) ++ " is :")
		   proves nbest
		   print_deductions nbao target
		  else do
		   putStr ("\n" ++ show (length nlvp) ++ " proofs")
		   putStr ("\nSize of biggest proof is " ++ show (sizeproof biggest))
		   proves biggest
		   putStr ("\nBest proof with value " ++ show (value nbest) ++ " is :")
		   proves nbest
		   print_deductions nbao target 
  
 print_deductions_1 bao = do
  case bao of 
   BestAndOther best lvp ->
    do
	  let nbao = deduce bao in
	   case nbao of
	    BestAndOther nbest nlvp ->
		 let biggest = biggest_of nlvp in
		  do
		   putStr ("\n" ++ show (length nlvp) ++ " proofs")
		   putStr ("\nSize of biggest proof is " ++ show (sizeproof biggest))
		   proves biggest
		   putStr ("\nBest proof with value " ++ show (value nbest) ++ " is :")
		   proves nbest 
		   display_lvp nlvp
 
 display_vp vp = case vp of
  ValuedProof x v -> do
   putStr ("Proof of value " ++ show v ++ " : " ++ show x ++ "\n")
	
 display_lvp [] = do return()
 
 display_lvp (vp : lvp) = do
  display_vp vp
  display_lvp lvp
  
 display_bao bao = case bao of
  BestAndOther best lvp -> do
   putStr ("\nBest proof with value " ++ show (value best) ++ " is :")
   proves best
   display_lvp lvp
   
 init_bao = 
  let lvp = map give_value axioms in
   let best = best_of lvp in
    let bao = BestAndOther best lvp in
	 bao
	 
 sort_bao bao = case bao of
  BestAndOther best lvp ->
   BestAndOther best (sort_proofs lvp)
   
 test_deduce_1 = do
  let lvp = map give_value axioms in
   let best = best_of lvp in
    let bao = BestAndOther best lvp in
     print_deductions_1 bao 
	 
 proofs_of_degree 0 = axioms
 
 proofs_of_degree n_plus_1 = let n = n_plus_1 - 1 in
  let lp = proofs_of_degree n in
      map (\x -> NXV x) lp
   ++ map (\x -> FNC x) lp
   ++ concat (flip map [0..n] (\p ->
       concat (flip map (proofs_of_degree p) (\y ->
	    concat (flip map (proofs_of_degree (n-p)) (\z -> 
		 [ APL y z, APL z y, LTR y z, LTR z y ] )) )) )) 
		 
 print_proofs [] = do return()
 
 print_proofs (x : lp) = do
  proves x
  print_proofs lp
  
 best_proof = foldr1 (\x -> \y -> if value x >= value y then x else y) 

 display_proof x = do
  putStr ("\nProof of value " ++ show (value x) ++ " :")
  proves x
  