module Test_callCC where

 import Control.Monad.Cont

 -- Returns a string depending on the length of the name parameter.
 -- If the provided string is empty, returns an error.
 -- Otherwise, returns a welcome message.
 whatsYourName :: String -> String
 whatsYourName name =
  (`runCont` id) $ do                      -- 1
    response <- callCC $ \exit -> do       -- 2
      validateName name exit               -- 3
      return $ "Welcome, " ++ name ++ "!"  -- 4
    return response                        -- 5

 validateName name exit = do
  when (null name) (exit "You forgot to tell me your name!")

 strReadFile :: String -> String
 strReadFile name =
  (`runCont` id) $ do                      -- 1
    response <- callCC $ \exit -> do       -- 2
      doReadFile name exit               -- 3
      return $ "Welcome, " ++ name ++ "!"  -- 4
    return response                        -- 5

 doReadFile name exit = do
  -- exit name
  readFile name >>= \s -> exit s

