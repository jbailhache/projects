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
  out <- openFile "ton_graph_wn_inc.tex" AppendMode
  hPutStr out (graph s r a)
  hPutStr out ("$" ++ l ++ "$ = $" ++ latex a ++ "$\n")

 main = do
  out <- openFile "ton_graph_wn_inc.tex" WriteMode
  pgraph "1 = suc\\ 0" (C O O) 6 0.8
  pgraph "2 = suc (suc\\ 0)" (C O (C O O)) 6 0.8
  pgraph "3 = suc (suc (suc\\ 0))" (C O (C O (C O O))) 6 0.8
  pgraph "\\omega = H suc\\ 0" (C (C O O) O) 6 0.8
  pgraph "\\omega+1 = suc (H suc\\ 0)" (C O (C (C O O) O)) 6 0.8
  pgraph "\\omega \\cdot 2 = H suc (H suc\\ 0)" (C (C O O) (C (C O O) O)) 10 0.6
  pgraph "\\omega \\cdot 2+1 = suc (H suc (H suc\\ 0))" (C O (C (C O O) (C (C O O) O))) 10 0.6
  pgraph "\\omega^2 = H (H suc) 0" (C (C O (C O O)) O) 6 0.8
  pgraph "\\omega^\\omega = H H suc\\ 0" (C (C (C O O) O) O) 6 0.8
  pgraph "\\text{In system 1, with } \\Omega = \\Omega_1 :$\n\n$\\varepsilon_0 = \\varphi(1,0) = \\varphi'(0,1) = Next\\ \\omega = R_1 H suc\\ 0" (C W O) 6 0.8
  pgraph "\\varepsilon_0+1 = suc (R_1 H suc\\ 0)" (C O (C W O)) 6 0.8
  pgraph "\\varepsilon_0+2 = suc (suc (R_1 H suc\\ 0))" (C O (C O (C W O))) 6 0.8
  pgraph "\\varepsilon_0+\\omega = H suc (R_1 H suc\\ 0)" (C (C O O) (C W O)) 10 0.6
  pgraph "\\varepsilon_0+\\omega \\cdot 2 = H suc (H suc (R_1 H suc\\ 0))" (C (C O O) (C (C O O) (C W O))) 10 0.6
  pgraph "\\varepsilon_0+\\omega^2 = H (H suc) (R_1 H suc 0)" (C (C O (C O O)) (C W O)) 6 0.8
  pgraph "\\varepsilon_0+\\omega^\\omega = H H suc (R_1 H suc 0))" (C (C (C O O) O) (C W O)) 10 0.6
  pgraph "\\varepsilon_0 \\cdot 2 = R_1 H suc (R_1 H suc\\ 0)" (C (C W O) (C W O)) 10 0.6
  pgraph "\\varepsilon_0 \\cdot 3 = R_1 H suc (R_1 H suc (R_1 H suc\\ 0))" (C (C W O) (C (C W O) (C W O))) 10 0.6
  pgraph "\\varepsilon_0 \\cdot \\omega = H (R_1 H suc) 0" (C (C O (C W O)) (C W O)) 10 0.6
  pgraph "\\varepsilon_0 \\cdot \\omega^2 = H (H (R_1 H suc)) 0" (C (C O (C O (C W O))) (C W O)) 10 0.6
  pgraph "\\varepsilon_0 \\cdot \\omega^\\omega = H H (R_1 H suc) 0" (C (C (C O O) (C W O)) (C W O)) 10 0.6
  pgraph "\\varepsilon_0 \\cdot \\omega^{\\omega^\\omega} = H H H (R_1 H suc) 0" (C (C (C (C O O) O) (C W O)) (C W O)) 10 0.6
  pgraph "{\\varepsilon_0}^2 = R_1 H (R_1 H suc) 0" (C (C (C W O) (C W O)) (C W O)) 10 0.6
  pgraph "{\\varepsilon_0}^3 = R_1 H (R_1 H (R_1 H suc)) 0" (C (C (C W O) (C (C W O) (C W O))) (C W O)) 10 0.6
  pgraph "{\\varepsilon_0}^\\omega = H (R_1 H) suc\\ 0" (C (C (C O (C W O)) (C W O)) (C W O)) 10 0.6
  pgraph "{\\varepsilon_0}^{\\omega^\\omega} = H H (R_1 H) suc\\ 0" (C (C (C (C O O) (C W O)) (C W O)) (C W O)) 10 0.6
  pgraph "{\\varepsilon_0}^{\\omega^{\\omega^\\omega}} = H H H (R_1 H) suc\\ 0" (C (C (C (C (C O O) O) (C W O)) (C W O)) (C W O)) 10 0.6
  pgraph "{\\varepsilon_0}^{\\varepsilon_0} = R_1 H (R_1 H) suc\\ 0" (C (C (C (C W O) (C W O)) (C W O)) (C W O)) 10 0.6
  pgraph "\\varepsilon_1 = \\varphi(1,1) = \\varphi'(0,2) = R_1 (R_1 H) suc\\ 0" (C W (C W O)) 6 0.8
  pgraph "\\varepsilon_\\omega = \\varphi(1,\\omega) = \\varphi'(0,\\omega) = H R_1 H suc\\ 0" (C (C O W) O) 6 0.8
  pgraph "\\varepsilon_{\\omega^2} = H (H R_1) H suc\\ 0" (C (C O (C O W)) O) 6 0.8
  pgraph "\\varepsilon_{\\omega^\\omega} = H H R_1 H suc\\ 0" (C (C (C O O) W) O) 6 0.8
  pgraph "\\varepsilon_{\\omega^{\\omega^\\omega}} = H H H R_1 H suc\\ 0" (C (C (C (C O O) O) W) O) 6 0.8
  pgraph "\\varepsilon_{\\varepsilon_0} = R_1 H R_1 H suc\\ 0" (C (C (C W O) W) O) 6 0.8
  pgraph "\\varepsilon_{\\varepsilon_{\\varepsilon_0}} = R_1 H R_1 H R_1 H suc\\ 0" (C (C (C (C (C W O) W) O) W) O) 6 0.8
  pgraph "\\zeta_0 = \\varphi(2,0) = \\varphi'(1,1) = [0] Next\\ \\omega = R_2 R_1 H suc\\ 0" (C (C W W) O) 6 0.8
  pgraph "\\zeta_1 = \\varphi(2,1) = \\varphi'(1,2) = R_2 R_1 (R_2 R_1 H) suc\\ 0" (C (C W W) (C (C W W) O)) 10 0.6
  pgraph "\\zeta_2 = \\varphi(2,2) = \\varphi'(1,3) = R_2 R_1 (R_2 R_1 (R_2 R_1 H)) suc\\ 0" (C (C W W) (C (C W W) (C (C W W) O))) 10 0.6
  pgraph "\\zeta_\\omega = \\varphi(2,\\omega) = \\varphi'(1,\\omega) = H (R_2 R_1) H suc\\ 0" (C (C O (C W W)) O) 10 0.6
  pgraph "\\zeta_{\\zeta_0} = R_2 R_1 H (R_2 R_1) H suc\\ 0" (C (C (C (C W W) O) (C W W)) O) 10 0.6
  pgraph "\\zeta_{\\zeta_\\omega} = H (R_2 R_1) H (R_2 R_1) H suc\\ 0" (C (C (C (C O (C W W)) O) (C W W)) O) 8 0.7
  pgraph "\\eta_0 = \\varphi(3,0) = \\varphi'(2,1) = R_2 (R_2 R_1) H suc\\ 0" (C (C W (C W W)) O) 6 0.8
  pgraph "\\varphi(\\omega,0) = \\varphi'(\\omega,1) = H R_2 R_1 H suc\\ 0" (C (C (C O W) W) O) 6 0.8
  pgraph "\\varphi(\\omega+1,0) = \\varphi'(\\omega+1,1) = R_2 (H R_2 R_1) H suc\\ 0" (C (C W (C (C O W) W)) O) 6 0.8 
  pgraph "\\varphi(\\omega \\cdot 2,0) = \\varphi'(\\omega \\cdot 2,1) = H R_2 (H R_2 R_1) H suc\\ 0" (C (C (C O W) (C (C O W) W)) O) 6 0.8
  pgraph "\\varphi(\\omega^2,0) = \\varphi'(\\omega^2,1) = H (H R_2) R_1 H suc\\ 0" (C (C (C O (C O W)) W) O) 6 0.8
  pgraph "\\varphi(\\omega^\\omega,0) = \\varphi'(\\omega^\\omega,1) = H H R_2 R_1 H suc\\ 0" (C (C (C (C O O) W) W) O) 6 0.8
  pgraph "\\varphi(\\omega^{\\omega^\\omega}) = \\varphi'(\\omega^{\\omega^\\omega}) = H H H R_2 R_1 H suc\\ 0" (C (C (C (C (C O O) O) W) W) O) 6 0.8
  pgraph "\\varphi(\\varepsilon_0,0) = \\varphi(\\varphi(1,0),0) = R_1 H R_2 R_1 H suc\\ 0" (C (C (C (C W O) W) W) O) 6 0.8
  pgraph "\\varphi(\\zeta_0,0) = \\varphi(\\varphi(2,0),0) = R_2 R_1 H R_2 R_1 H suc\\ 0" (C (C (C (C (C W W) O) W) W) O) 6 0.8 
  pgraph "\\varphi(\\varphi(\\omega,0),0) = H R_2 R_1 H R_2 R_1 H suc\\ 0" (C (C (C (C (C (C O W) W) O) W) W) O) 6 0.8 
  pgraph "\\varphi(\\varphi(\\varepsilon_0,0),0) = \\varphi(\\varphi(\\varphi(1,0),0),0) = R_1 H R_2 R_1 H R_2 R_1 H suc\\ 0" (C (C (C (C (C (C (C W O) W) W) O) W) W) O) 6 0.8
  pgraph "\\Gamma_0 = \\varphi(1,0,0) = \\varphi'(1,0,1) = [1] [0] Next\\ \\omega = R_3 R_2 R_1 H suc\\ 0" (C (C (C W W) W) O) 6 0.8
  pgraph "\\Gamma_1 = \\varphi(1,0,1) = \\varphi'(1,0,2) = R_3 R_2 R_1 (R_3 R_2 R_1 H) suc\\ 0" (C (C (C W W) W) (C (C (C W W) W) O)) 10 0.6
  pgraph "\\Gamma_\\omega = \\varphi(1,0,\\omega) = \\varphi'(1,0,\\omega) = H (R_3 R_2 R_1) H suc\\ 0" (C (C O (C (C W W) W)) O) 6 0.8
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

  pgraph "\\text{In system 2, with } \\Omega = \\Omega_2 :$\n\n$\\text{LVO} = [2] [1] [0] Next\\ \\omega = R_4 R_3 R_2 R_1 H suc\\ 0" (C (C (C (C (C W O) (C W O)) (C W O)) (C W O)) O) 20 0.6
  pgraph "\\text{BHO} = [\\omega \\ldots 0] Next\\ \\omega = R_{\\omega \\ldots 1} H suc\\ 0" (C (C W (C W O)) O) 6 0.8 
  pgraph "\\text{TFBO}" (C (C W (C (C O W) O)) O) 10 0.6

  pgraph "|\\Pi^{1}_1-\\text{CA}_0|_{\\text{Con}} = |\\Delta^{1}_2-\\text{CA}_0|_{\\text{Con}}" (C (C (C O W) O) O) 10 0.8
  pgraph "|\\Pi^1_1-\\text{CA}|_{\\text{Con}}" (C (C (C (C (C W O) O) (C (C O W) O)) (C (C O W) O)) O) 30 0.5
  pgraph "|\\Pi^{1}_1-\\text{CA}+\\text{BI}|_{\\text{Con}}" (C (C W (C (C O W) O)) O) 10 0.8
  pgraph "|\\Pi^{1}_1-\\text{TR}_0|_{\\text{Con}}" (C (C (C W W) O) O) 10 0.8
  pgraph "|\\Delta^{1}_2-\\text{CA}+\\text{BI}|_{\\text{Con}} = |\\text{KPi}|_{\\text{Con}}" (C (C (C (C (C (C W (C (C W W) O)) W) O) (C W W)) O) O) 20 0.8
  pgraph "|\\text{KP}|_{\\text{Con}}" (C (C W (C W O)) O) 10 0.8
  pgraph "|\\text{ML}_1\\text{W}|_{\\text{Con}}" (C (C (C (C (C (C O W) (C (C W (C (C W W) O)) W)) O) (C W W)) O) O) 20 0.75
  pgraph "|\\text{KPh}|_{\\text{Con}}" (C (C (C (C (C (C (C W (C (C W W) O)) (C W (C (C W W) O))) W) O) (C W W)) O) O) 20 0.75
  pgraph "|\\text{KPM}^+|_{\\text{Con}}" (C (C (C (C (C (C O W) (C (C (C (C W (C (C W W) O)) (C W (C (C W W) O))) (C W (C (C W W) O))) W)) O) (C W W)) O) O) 60 0.7
  pgraph "|\\text{KP}+\\Pi_3 - \\text{Reflection}|_{\\text{Con}}$\n\n$ " (C (C (C (C (C (C (C (C (C W (C (C W W) O)) (C W (C (C W W) O))) (C W (C (C W W) O))) (C W (C (C W W) O))) W) O) (C W W)) O) O) 60 0.7

