module Test where

 test = do
       putStrLn "Greetings!  What is your name?"
       inpStr <- getLine
       putStrLn $ "Welcome to Haskell, " ++ inpStr ++ "!"

 test2 = do
  putStrLn "Greetings! What is your name?" 
  getLine >>= \inpStr -> do 
   putStrLn $ "Welcome to Haskell, " ++ inpStr ++ "!"

