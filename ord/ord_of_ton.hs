module Main where

 ident x = x

 comp f g x = f (g x)

 data Ord 
  = Zero
  | Suc Ord
  | Lim Integer (Ord -> Ord)

 one = Suc Zero
 two = Suc one
 three = Suc two

 show_ord n Zero = "0"
 show_ord n (Suc a) = "S " ++ show_ord (n+2) a
 show_ord n (Lim k f) = "L" ++ show k ++ " " ++ show_ord (n+3) (f Zero) ++ "\n" ++ replicate (n+3) ' ' ++ show_ord (n+3) (f one) ++ "\n" ++ replicate (n+3) ' ' ++ show_ord (n+3) (f two) -- ++ "\n" ++ replicate (n+3) ' ' ++ show_ord (n+3) (f three)

 instance Show Ord where
  show a = show_ord 0 a

  -- Definition of ordinals in Taranovsky Ordinal Notation 
 data Ton = O | W | C Ton Ton
  deriving (Eq, Show)

 ord_of_int 0 = Zero
 ord_of_int (n+1) = Suc (ord_of_int n)

 -- power of a function : fpower0 a f = f^a
 fpower0 Zero f = ident
 fpower0 (Suc a) f = comp f (fpower0 a f)
 fpower0 (Lim n g) f = \x -> Lim n (\y -> fpower0 (g y) f x)

 level Zero = 0
 level (Suc a) = level a
 level (Lim k f) = k

 c n Zero a = Suc a
 c n (Suc a) b = Lim 0 (\i -> fpower0 i (c n a) b)
 c n (Lim k f) b = if level (Lim k f) <= level b
                   then Lim k (\x -> c n (f x) b)
                   else Lim 0 (\i -> fpower0 i (\x -> c n (f x) b) Zero)

 ord_of_ton n O = Zero
 ord_of_ton n W = Lim n ident
 ord_of_ton n (C a b) = c n (ord_of_ton n a) (ord_of_ton n b)

 -- Large ordinals
 data Lord
  = Lzero
  | Lsuc Lord
  | Llim Lord (Lord -> Lord)

 show_lord n Lzero = "0"
 show_lord n (Lsuc a) = "S " ++ show_lord (n+2) a
 show_lord n (Llim k f) = "L" ++ show k ++ " " ++ show_lord (n+3) (f Lzero) ++ "\n" ++ replicate (n+3) ' ' ++ show_lord (n+3) (f (Lsuc Lzero)) ++ "\n" ++ replicate (n+3) ' ' ++ show_lord (n+3) (f (Lsuc (Lsuc Lzero))) -- ++ "\n" ++ replicate (n+3) ' ' ++ show_ord (n+3) (f three)

 instance Show Lord where
  show a = show_lord 0 a
 
 lord_of_int 0 = Lzero
 lord_of_int (n+1) = Lsuc (lord_of_int n)

 int_of_lord Lzero = 0
 int_of_lord (Lsuc a) = int_of_lord a + 1

 ord_of_lord Lzero = Zero
 ord_of_lord (Lsuc a) = Suc (ord_of_lord a)
 ord_of_lord (Llim k f) = Lim (int_of_lord k) (\x -> ord_of_lord (f (lord_of_ord x)))

 lord_of_ord Zero = Lzero
 lord_of_ord (Suc a) = Lsuc (lord_of_ord a)
 lord_of_ord (Lim k f) = Llim (lord_of_int k) (\x -> lord_of_ord (f (ord_of_lord x)))

