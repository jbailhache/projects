module Main where
 
 import System.IO

 -- Definition of ordinals in Taranovsky Ordinal Notation 
 data Ton = O | W | W2 | C Ton Ton
  deriving (Eq, Show)


 latex O = "0"
 latex W = "\\Omega"
 latex W2 = "\\Omega_2"
 latex (C a b) = "C(" ++ latex a ++ "," ++ latex b ++ ")"

 --graph1 x y s r O = "\\put(" ++ show x ++ "," ++ show y ++ "){$0$}\n"
 graph1 x y s r O = "\\put(" ++ show x ++ "," ++ show y ++ "){\\circle{2}}\n"

 --graph1 x y s r W = "\\put(" ++ show x ++ "," ++ show y ++ "){$\\Omega$}\n"
 graph1 x y s r W = "\\put(" ++ show x ++ "," ++ show y ++ "){\\circle*{2}}\n"

 graph1 x y s r W2 = "\\put(" ++ show x ++ "," ++ show y ++ "){\\circle*{2}}\n\\put(" ++ show x ++ "," ++ show y ++ "){\\circle{4}}\n"

 graph1 x y s r (C a b) = "\\put(" ++ show x ++ "," ++ show y ++ "){\\line(0,1){" ++ show s ++ "}}\n" ++ "\\put(" ++ show x ++ "," ++ show y ++ "){\\line(1,0){" ++ show s ++ "}}\n" ++ graph1 x  (y+s) (r*s) r a ++ graph1 (x+s) y (r*s) r b

 graph s r a = let t = s * (1 / r) / ((1 / r) - 1) in
  "\n\\setlength{\\unitlength}{1mm}\n\\begin{picture}(" ++ show t ++ "," ++ show t ++ ")\n" ++ graph1 0 0 s r a ++ "\\end{picture}\n\n"

 pgraph l a s r =  do
  out <- openFile "ton_graph_wn_bho_inc.tex" AppendMode
  hPutStr out (graph s r a)
  hPutStr out ("$" ++ l ++ "$ = $" ++ latex a ++ "$\n")

 main = do
  out <- openFile "ton_graph_wn_bho_inc.tex" WriteMode

  pgraph "\\varepsilon_0 = \\varphi(1,0) = \\varphi'(0,1) = Next\\ \\omega = R_1 H suc\\ 0" (C W O) 6 0.8
  pgraph "\\zeta_0 = \\varphi(2,0) = \\varphi'(1,1) = [0] Next\\ \\omega = R_2 R_1 H suc\\ 0" (C (C W W) O) 6 0.8
  pgraph "\\Gamma_0 = \\varphi(1,0,0) = \\varphi'(1,0,1) = [1] [0] Next\\ \\omega = R_3 R_2 R_1 H suc\\ 0" (C (C (C W W) W) O) 6 0.8
  pgraph "\\text{LVO} = [2] [1] [0] Next\\ \\omega = R_4 R_3 R_2 R_1 H suc\\ 0" (C (C (C (C W W) W) W) O) 6 0.8
  pgraph "\\text{BHO} = [\\omega \\ldots 0] Next\\ \\omega = R_{\\omega \\ldots 1} H suc\\ 0" (C (C W2 W) O) 6 0.8 
  pgraph "BHO \\cdot 2 =  R_{\\omega \\ldots 1} H suc (R_{\\omega \\ldots 1} H suc\\ 0)" (C (C (C W2 W) O) (C (C W2 W) O)) 10 0.6
  pgraph "BHO^2 = R_{\\omega \\ldots 1} H (R_{\\omega \\ldots 1} H suc) 0" (C (C (C (C W2 W) O) (C (C W2 W) O)) (C (C W2 W) O)) 12 0.5
  pgraph "BHO^{BHO} = R_{\\omega \\ldots 1} H (R_{\\omega \\ldots 1} H) suc\\ 0" (C (C (C (C (C W2 W) O) (C (C W2 W) O)) (C (C W2 W) O)) (C (C W2 W) O)) 20 0.5
  pgraph "\\varepsilon_{BHO+1} = R_1 (R_{\\omega \\ldots 1} H) suc\\ 0" (C W (C (C W2 W) O)) 6 0.8
  pgraph "\\varepsilon_{BHO+2} = R_1 (R_1 (R_{\\omega \\ldots 1} H)) suc\\ 0" (C W (C W (C (C W2 W) O))) 6 0.8
  pgraph "\\varepsilon_{BHO+\\varepsilon_{BHO+1}} = R_1 (R_{\\omega \\ldots 1} H) R_1 (R_{\\omega \\ldots 1} H) suc\\ 0" (C (C (C W (C (C W2 W) O)) W) (C (C W2 W) O)) 10 0.6
  pgraph "\\zeta_{BHO+1} = R_2 R_1 (R_{\\omega \\ldots 1} H) suc\\ 0" (C (C W W) (C (C W2 W) O)) 6 0.8
  pgraph "R_{\\omega \\ldots 1} (R_{\\omega \\ldots 1} H) suc\\ 0" (C (C W2 W) (C (C W2 W) O)) 6 0.8
  pgraph "H R_{\\omega \\ldots 1} H suc\\ 0" (C (C O (C W2 W)) (C (C W2 W) O)) 12 0.5
  pgraph "R_{\\omega \\ldots 1} H R_{\\omega \\ldots 1} H suc\\ 0" (C (C (C (C W2 W) O) (C W2 W)) O) 10 0.6
  pgraph "R_2 R_{\\omega \\ldots 1} H suc\\ 0" (C (C W (C W2 W)) O) 6 0.8
  pgraph "R_3 R_2 R_{\\omega \\ldots 1} H suc\\ 0" (C (C (C W W) (C W2 W)) O) 10 0.6
  pgraph "R_4 R_3 R_2 R_{\\omega \\ldots 1} H suc\\ 0" (C (C (C (C W W) W) (C W2 W)) O) 10 0.6
  pgraph "R_{\\omega \\ldots 2} R_{\\omega \\ldots 1} H suc\\ 0" (C (C (C W2 W) (C W2 W)) O) 10 0.6 
  pgraph "R_{\\omega \\ldots 3} R_{\\omega \\ldots 2} R_{\\omega \\ldots 1} H suc\\ 0 = R_{\\omega \\cdot 3 \\ldots 1} H suc\\ O" (C (C (C W2 W) (C (C W2 W) (C W2 W))) O) 20 0.5 
  pgraph "R_{\\omega^2 \\ldots 1} H suc\\ 0" (C (C (C O (C W2 W)) (C W2 W)) O) 10 0.6
  pgraph "R_{\\omega^3 \\ldots 1} H suc\\ 0" (C (C (C O (C O (C W2 W))) (C W2 W)) O) 20 0.5
  pgraph "R_{\\omega^\\omega \\ldots 1} H suc\\ 0" (C (C (C (C O O) (C W2 W)) (C W2 W)) O) 10 0.6
  pgraph "R_{\\omega^{\\omega^\\omega} \\ldots 1} H suc\\ 0" (C (C (C (C (C O O) O) (C W2 W)) (C W2 W)) O) 10 0.6
  pgraph "R_{\\varepsilon_0 \\ldots 1} H suc\\ 0" (C (C (C (C W O) (C W2 W)) (C W2 W)) O) 10 0.6
  pgraph "R_{\\zeta_0 \\ldots 1} H suc\\ 0" (C (C (C (C (C W W) O) (C W2 W)) (C W2 W)) O) 10 0.6
  pgraph "R_{\\Gamma_0 \\ldots 1} H suc\\ 0" (C (C (C (C (C (C W W) W) O) (C W2 W)) (C W2 W)) O) 16 0.6
  pgraph "R_{BHO \\ldots 1} H suc\\ 0 = R_{R_{\\omega \\ldots 1} H suc\\ 0 \\ldots 1} H suc\\ 0" (C (C (C (C (C W2 W) O) (C W2 W)) (C W2 W)) O) 20 0.6
  pgraph "R_{R_{R_{\\omega \\ldots 1} H suc\\ O \\ldots 1} H suc\\ 0 \\ldots 1} H suc\\ 0" (C (C (C (C (C (C (C (C W2 W) O) (C W2 W)) (C W2 W)) O) (C W2 W)) (C W2 W)) O) 20 0.8
  pgraph "H [R_{\\bullet \\ldots 1} H suc\\ 0] 0" (C (C (C W (C W2 W)) (C W2 W)) O) 10 0.6 

