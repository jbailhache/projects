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
  out <- openFile "ocf_and_ton_graph_inc.tex" AppendMode
  hPutStr out (graph s r a)
  hPutStr out ("$" ++ l ++ "$ = $" ++ latex a ++ "$\n")

 main = do
  out <- openFile "ocf_and_ton_graph_inc.tex" WriteMode

  pgraph "a = C(\\Omega_2 2,0) = C(C(\\Omega_2,\\Omega_2),0)" (C (C W2 W2) O) 6 0.8
  pgraph "d = C(\\Omega_2,C(C(\\Omega_2,\\Omega_2),0))" (C W2 (C (C W2 W2) O)) 6 0.8
  pgraph "I = C(\\Omega_2+d,0) = C(C(d,\\Omega_2),0)" (C (C (C W2 (C (C W2 W2) O)) W2) O) 6 0.8
  pgraph "M = C(\\Omega_2+d^2,0) = C(C(C(C(d,d),0),\\Omega_2),0)" (C (C (C (C (C W2 (C (C W2 W2) O)) (C W2 (C (C W2 W2) O))) O) W2) O) 10 0.8
  pgraph "\\Psi^{CK}_I(I) = C(\\Omega_2+a 2) = C(C(a,C(a,\\Omega_2)),0)" (C (C (C (C W2 W2) O) (C (C (C W2 W2) O) W2)) O) 10 0.8
  pgraph "\\Psi(\\Psi_I(0) = C(C(\\Omega_2 2,0),0) = C(C(C(\\Omega_2,\\Omega_2),0),0)" (C (C (C W2 W2) O) O) 10 0.8
  pgraph "\\Psi(\\Psi_I(I))" (C (C (C (C (C (C (C W2 W2) O) (C (C (C W2 W2) O) W2)) O) (C W2 W2)) O) O) 10 0.8
 