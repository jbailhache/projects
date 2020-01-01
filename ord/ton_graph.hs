module Main where

 import Data.Typeable
 
 -- Definition of ordinals in Taranovsky Ordinal Notation 
 data Ton = O | W | C Ton Ton
  deriving (Eq, Show)

 -- Item of postfix representation
 data PostfixItem = CP | OP | WP
  deriving (Eq, Show, Ord)

 -- Convert to postscript representation
 postfix O = [ OP ]
 postfix W = [ WP ]
 postfix (C a b) = postfix b ++ postfix a ++ [ CP ]

 -- short representation of postfix form
 string_postfix [] = ""
 string_postfix (CP:l) = "C" ++ string_postfix l
 string_postfix (OP:l) = "O" ++ string_postfix l
 string_postfix (WP:l) = "W" ++ string_postfix l

 -- Compare ordinals by comparing postfix representations
 instance Ord Ton where
  compare a b = compare (postfix a) (postfix b)

 -- List of subterms of an ordinal
 subterms O = [ O ]
 subterms W = [ W ]
 subterms (C a b) = [ C a b ] ++ subterms a ++ subterms b

 -- nbfbf n a b : a is n-built from below from b 
 nbfbf 0 a b = a <= b                    -- a is O-BFB from b if and only if a<b
 nbfbf n1 a b = let n = n1-1 in          -- a is (n+1)-BFB from b if and only if:
  flip all (subterms a) (\c ->           --  for all subterm c of a,
   c <= a ||                             --   either c <= a
   flip any (subterms a) (\d ->          --   or there exists subterms d of a such that
    elem c (subterms d) && nbfbf n d b)) --    c is a subterm of d and d is n-BFB from b

 -- standard n a : a is in standard form in n-th system
 standard _ O = True    -- 0 is standard
 standard _ W = True    -- W is standard
 standard n (C a b) =   -- C(a,b) is standard if and only if :
  standard n a &&       --  a is standard
  standard n b &&       --  b is standard
  (case b of            --  b is 0 or W or C(c,d) with a <= c
    O -> True
    W -> True
    C c d -> a <= c) &&
  nbfbf n a (C a b)     -- a is n-BFB from C(a,b)

 -- list_ton_l l = list of ordinals with l C's in their representation
 list_ton_l 0 = [ O, W ]
 list_ton_l k1 = let k = k1-1 in 
  concat (flip map [0..k] (\l ->
   concat (flip map (list_ton_l l) (\c -> 
    concat (flip map (list_ton_l (k-l)) (\d -> 
     [ C c d ] )) )) ))

 -- fs n a k = k-th element of findamental sequence of a in n-th system
 -- a[k] = max { b | L(b) = k, b is standard and b < a }
 fs n a k = foldr (\x -> \y -> if (x <= y) then y else x) O
             (flip filter (list_ton_l k) (\b -> (standard n b) && (b < a)))
 
 printfs1 n a i j = 
  if i > j
  then return True
  else do
   putStr ("[" ++ (show i) ++ "] " ++ (show (fs n a i)) ++ "\n")
   printfs1 n a (i+1) j
   return True 
   
 printfs name n a i j = do
  putStr (name ++ " n=" ++ show n ++ "\n" ++ show a ++ "\n")
  printfs1 n a i j
  putStr "\n"
  
 -- ccnvert to 0 suc lim
 
 ident x = x
 
 data On 
  = Zero
  | Suc On
  | Lim On (On -> On)
  
 intofon Zero = 0
 intofon (Suc a) = intofon a + 1
  
 onofton n O = Zero
 onofton n W = Lim (Suc Zero) ident
 onofton n (C O b) = Suc (onofton n b)
 onofton n (C a b) = 
  Lim Zero (\k -> onofton n (fs n (C a b) (intofon k)))
  
 -- main = print (fs 1 (C (C O O) O) 3)
 
 explore = do
  printfs "w"     1 (C (C O O) O) 1 3				
  printfs "w.2"   1 (C (C O O) (C (C O O) O)) 1 5
  printfs "w^2"   1 (C (C O (C O O)) O) 1 6
  printfs "w^w"   1 (C (C (C O O) O) O) 1 6
  printfs "e_0"   1 (C W O) 1 6
  printfs "e_0"   2 (C (C W O) O) 1 6
  printfs "e_0.2" 1 (C (C W O) (C W O)) 1 6
  printfs "z_0"   1 (C (C W W) O) 1 6
  printfs "z_0"   2 (C (C (C W O) (C W O)) O) 1 6
  printfs "G_0"   1 (C (C (C W W) W) O) 1 6
  printfs "LVO"   1 (C (C (C (C W W) W) W) O) 1 6
  printfs "BHO"   2 (C (C W (C W O)) O) 1 6
    
 latex O = "0"
 latex W = "\\Omega"
 latex (C a b) = "C(" ++ latex a ++ "," ++ latex b ++ ")"

 graph1 x y s r O = "\\put(" ++ show x ++ "," ++ show y ++ "){$0$}\n"
 graph1 x y s r W = "\\put(" ++ show x ++ "," ++ show y ++ "){$\\Omega$}\n"
 graph1 x y s r (C a b) = "\\put(" ++ show x ++ "," ++ show y ++ "){\\line(0,1){" ++ show s ++ "}}\n" ++ "\\put(" ++ show x ++ "," ++ show y ++ "){\\line(1,0){" ++ show s ++ "}}\n" ++ graph1 x  (y+s) (r*s) r a ++ graph1 (x+s) y (r*s) r b

 graph s r a = let t = s * (1 / r) / ((1 / r) - 1) in
  "\n\\setlength{\\unitlength}{1mm}\n\\begin{picture}(" ++ show t ++ "," ++ show t ++ ")\n" ++ graph1 0 0 s r a ++ "\\end{picture}\n\n"
--  "Graphical representation of $" ++ latex a ++ "$ :\n\n\\setlength{\\unitlength}{1mm}\n\\begin{picture}(" ++ show t ++ "," ++ show t ++ ")\n" ++ graph1 0 0 s r a ++ "\\end{picture}\n"

 pgraph l a s r =  do
  putStr (graph s r a)
  putStr ("$" ++ l ++ "$ = $" ++ latex a ++ "$\n")

 main = do
  pgraph "|\\Pi^{1}_1-\\text{CA}_0|_{\\text{Con}} = |\\Delta^{1}_2-\\text{CA}_0|_{\\text{Con}}" (C (C (C O W) O) O) 10 0.8
  pgraph "|\\Pi^1_1-\\text{CA}|_{\\text{Con}}" (C (C (C (C (C W O) O) (C (C O W) O)) (C (C O W) O)) O) 30 0.5
  pgraph "|\\Pi^{1}_1-\\text{CA}+\\text{BI}|_{\\text{Con}}" (C (C W (C (C O W) O)) O) 10 0.8
  pgraph "|\\Pi^{1}_1-\\text{TR}_0|_{\\text{Con}}" (C (C (C W W) O) O) 10 0.8
  pgraph "|\\Delta^{1}_2-\\text{CA}+\\text{BI}|_{\\text{Con}} = |\\text{KPi}|_{\\text{Con}}" (C (C (C (C (C (C W (C (C W W) O)) W) O) (C W W)) O) O) 20 0.8
  pgraph "|\\text{KP}|_{\\text{Con}}" (C (C W (C W O)) O) 10 0.8
  pgraph "|\\text{ML}_1\\text{W}|_{\\text{Con}}" (C (C (C (C (C (C O W) (C (C W (C (C W W) O)) W)) O) (C W W)) O) O) 20 0.75
  pgraph "|\\text{KPh}|_{\\text{Con}}" (C (C (C (C (C (C (C W (C (C W W) O)) (C W (C (C W W) O))) W) O) (C W W)) O) O) 20 0.75
  pgraph "|\\text{KPM}^+|_{\\text{Con}}" (C (C (C (C (C (C O W) (C (C (C (C W (C (C W W) O)) (C W (C (C W W) O))) (C W (C (C W W) O))) W)) O) (C W W)) O) O) 60 0.7
  pgraph "|\\text{KP}+\\Pi_3 - \\text{Reflection}|_{\\text{Con}}" (C (C (C (C (C (C (C (C (C W (C (C W W) O)) (C W (C (C W W) O))) (C W (C (C W W) O))) (C W (C (C W W) O))) W) O) (C W W)) O) O) 60 0.7
  -- (C (C (C (C (C (C (C (C (C W (C (C W W) O)) (C W (C (C W W) O))) (C W (C (C W W)      (C W (C (C W W) O))) W) O) (C W W)) O) O) 60 0.7
  -- pgraph "|\\text{KP}+\\Pi_{n+2}-\\text{Reflection}|_{\\text{Con}}" (C (C (C (C (C (C (C (C (C (C O (C W (C (C W W) O))) (C W (C (C W W) O))) (C W (C (C (C W (C (C W W) O))) (C W (C (C W W) O))) w) O) (C W W)) O) O) 60 0.7

 a1 = C (C (C O W) O) O

 a2 = C (C (C (C (C W O) O) (C (C O W) O)) (C (C O W) O)) O

 a3 = C (C W (C (C O W) O)) O

 a4 = C (C (C W W) O) O

 a5 = C (C (C (C (C (C W (C (C W W) O)) W) O) (C W W)) O) O

