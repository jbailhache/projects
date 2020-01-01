module TreeOrd where

 data Nat = ZeroN | SucN Nat

 -- data TreeOrd n
 --  = Zero
 --  | Suc (TreeOrd n)
 --  | Lim (TreeOrd k -> TreeOrd n)

 data TreeOrd0 
  = Zero0
  | Suc0 TreeOrd0 

 data TreeOrd1
  = Zero1
  | Suc1 TreeOrd1
  | Lim1 (TreeOrd0 -> TreeOrd1)

 data TreeOrd2
  = Zero2
  | Suc2 TreeOrd2
  | Lim02 (TreeOrd0 -> TreeOrd2)
  | Lim12 (TreeOrd1 -> TreeOrd2)

