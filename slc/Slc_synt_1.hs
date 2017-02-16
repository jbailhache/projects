module Slc_synt where

 import Slcn

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

