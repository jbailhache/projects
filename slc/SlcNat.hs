module SlcNat where

 import Slcn


 t = lambda "x" $ lambda "y" (var "x")
 f = lambda "x" $ lambda "y" (var "y")

 combk = lambda "x" $ lambda "y" (var "x")


 sr_0 = lambda "z" $ lambda "s" (var "z")
 sr_suc = lambda "n" $ lambda "z" $ lambda "s" $ apl (var "s") (var "n")

 fr_0 = lambda "z" $ lambda "s" (var "z")
 fr_suc = lambda "n" $ lambda "z" $ lambda "s" $ apl (var "s") $ apl2 (var "n") (var "z") (var "s")
 fr_succ = lambda "n" $ lambda "z" $ lambda "s" $ apl2 (var "n") (apl (var "s") (var "z")) (var "s")

 sr_of_fr = lambda "fr" $ apl2 (var "fr") sr_0 sr_suc

 fr_of_sr = lambda "sr" $ apl2 (var "sr") fr_0 $ lambda "p" $ lambda "z" $ lambda "s" $ apl (var "s") $ apl2 (var "p") (var "z") (var "s")

 sr_1 = reduce $ apl sr_suc sr_0
 sr_2 = reduce $ apl sr_suc sr_1
 sr_3 = reduce $ apl sr_suc sr_2

 fr_1 = reduce $ apl fr_suc fr_0
 fr_2 = reduce $ apl fr_suc fr_1
 fr_3 = reduce $ apl fr_suc fr_2


 sr_plus = fix $ lambda "sr_plus" $ lambda "n" $ lambda "p" $ 
  apl2 (var "n") (var "p") $ lambda "m" $ apl sr_suc $ apl2 (var "sr_plus") (var "m") (var "p")

 fr_plus = lambda "n" $ lambda "p" $ apl2 (var "n") (var "p") fr_suc


 sr_null = lambda "n" $ apl2 (var "n") t (lambda "p" f)

 fr_null = lambda "n" $ apl2 (var "n") t (lambda "r" f) 


 sr_pred = lambda "n" $ apl2 (var "n") sr_0 (lambda "p" (var "p"))

 fr_pred = lambda "n" $ apl fr_of_sr $ apl sr_pred $ apl sr_of_fr (var "n")

 sr_eq = fix $ lambda "sr_eq" $ lambda "a" $ lambda "b" $ apl2 (var "a")
  (apl2 (var "b") t (lambda "b1" f))
  (lambda "a1" $ apl2 (var "b") f (lambda "b1" $ apl2 (var "sr_eq") (var "a1") (var "b1")))

