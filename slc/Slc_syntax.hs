module Slc_syntax where

 import Slcn

 split1 d w [] = [w]
 split1 d w (x : s) = if elem x d then (if w == [] then split1 d [] s else w : split1 d [] s) else split1 d (w ++ [x]) s

 split d s = split1 d [] s

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


 slc1 ("AXM" : s) = (axm, s)
 slc1 ("DB0" : s) = (db0, s)
 slc1 ("DBS" : s) = let (x, t) = slc1 s in (dbs x, t)
 slc1 ("DBL" : s) = let (x, t) = slc1 s in (dbl x, t)
 slc1 ("APL" : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (apl x y, u)
 slc1 ("LTR" : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (ltr x y, u)
 slc1 ("EQU" : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (equ x y, u)
 slc1 ("LET" : v : s) = let (x, t) = slc1 s in let (y, u) = slc1 t in (apl (lambda v y) x, u)
 slc1 (w : s) = (smb w, s)

 -- slc s = let (x, t) = slc1 (split " " s) in if t == [] then Just x else Nothing
 slc s = let (x, t) = slc1 (split " " s) in if t == [] then x else smb ("Error : Unexpected '" ++ head t ++ "'")

 
