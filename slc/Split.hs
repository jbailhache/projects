module Split where

 import Data.List
 import Data.Char

 split1 d w [] = [w]
 split1 d w (x : s) = if elem x d then (if w == [] then split1 d [] s else w : split1 d [] s) else split1 d (w ++ [x]) s

 split d s = split1 d [] s

