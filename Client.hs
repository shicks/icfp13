{-# LANGUAGE ViewPatterns #-}

module Client where

import Program

import Debug.Trace ( trace )
import Data.Char ( toUpper )
import Data.Word ( Word64 )
import Network.HTTP ( Response(..), postRequestWithBody, simpleHTTP )
import Numeric ( showHex )
import Text.JSON ( JSObject, JSON(..), JSValue(..), Result(..),
                   decode, encode, fromJSObject, makeObj )


data Problem = Problem { problemId :: String, 
                         problemSize :: Int, 
                         problemOperators :: [String], 
                         problemSolved :: Maybe Bool, 
                         problemTime :: Maybe Int }
             deriving ( Show )

instance JSON Problem where
  readJSON (JSObject (fromJSObject -> o)) = do id <- lookup' "id" o
                                               size <- lookup' "size" o
                                               ops <- lookup' "operators" o
                                               solved <- lookupMaybe "solved" o
                                               time <- lookupMaybe "timeLeft" o
                                               return $ Problem id size ops solved time
  showJSON _ = error "No need to serialize a Problem"

data EvalRequest = EvalProblem String [Word64] | EvalProgram String [Word64]
                 deriving ( Show )
data EvalResponse = EvalOk [Word64] | EvalError String
                  deriving ( Show )

instance JSON EvalRequest where
  readJSON _ = error "No need to deserialize an EvalRequest"
  showJSON (EvalProblem id args) = makeObj [("id", showJSON id), 
                                            ("arguments", showJSON $ map toHex args)]
  showJSON (EvalProgram program args) = makeObj [("program", showJSON program), 
                                                 ("arguments", showJSON $ map toHex args)]

tr s x = trace (s ++ " = " ++ show x) x

instance JSON EvalResponse where
  readJSON (JSObject (fromJSObject -> o)) = 
    do status <- lookup' "status" o
       case status of
         "ok" -> (EvalOk . map read . tr "resp") `fmap` lookup' "outputs" o
         "error" -> EvalError `fmap` lookup' "message" o
         _ -> fail $ "Unknown status: " ++ status
  showJSON _ = error "No need to serialize an EvalResponse"

data Guess = Guess String String
           deriving ( Show )
data GuessResponse = Win | Mismatch Word64 Word64 Word64 | GuessError String

instance JSON Guess where
  readJSON _ = error "No need to deserialize a Guess"
  showJSON (Guess id program) = makeObj [("id", showJSON id), 
                                         ("program", showJSON program)]

instance JSON GuessResponse where
  readJSON (JSObject (fromJSObject -> o)) =
    do status <- lookup' "status" o
       case status of
         "win" -> return Win
         "mismatch" -> do (arg, expected, actual) <- lookup' "values" o
                          return $ Mismatch arg expected actual
         "error" -> GuessError `fmap` lookup' "message" o
         _ -> fail $ "Unknown status: " ++ status
  showJSON _ = error "No need to serialize a GuessResponse"

instance Show GuessResponse where
  show Win = "Win"
  show (Mismatch arg expected actual) = "Mismatch: P(" ++ show arg ++ ") = " ++ 
                                        show expected ++ " but you got " ++ show actual
  show (GuessError msg) = "GuessError " ++ msg

data TrainRequest = TrainRequest (Maybe Int) String
                  deriving ( Show )
data TrainingProblem = TrainingProblem { trainingChallenge :: String, 
                                         trainingId :: String, 
                                         trainingSize :: Int, 
                                         trainingOperators :: [String] }
                     deriving ( Show )

instance JSON TrainRequest where
  readJSON _ = error "No need to deserialize a TrainRequest"
  showJSON (TrainRequest (Just size) ops) = makeObj [("size", showJSON size), 
                                                     ("operators", showJSON ops)]
  showJSON (TrainRequest Nothing ops) = makeObj [("operators", showJSON ops)]
                                            
instance JSON TrainingProblem where  
  readJSON (JSObject (fromJSObject -> o)) = do soln <- lookup' "challenge" o
                                               id <- lookup' "id" o
                                               size <- lookup' "size" o
                                               ops <- lookup' "operators" o
                                               return $ TrainingProblem soln id size ops
  showJSON _ = error "No need to serialize a TrainingProblem"

auth :: String
auth = "03322ZfXM9y7bAmubitseHsbGtSyUBS8Uqvv9YmBvpsH1H"

-- Note: We could use a simple body-less POST here, but we already have it
myProblems :: IO [Problem]
myProblems = readFile "myproblems.txt" >>= unResult . decode

train :: TrainRequest -> IO TrainingProblem
train = rpc "train"

toProblem :: TrainingProblem -> Problem
toProblem (TrainingProblem _ i s o) = Problem i s o Nothing Nothing

eval :: EvalRequest -> IO [Word64]
eval req = do response <- rpc "eval" req
              case response of
                EvalOk a -> return a
                EvalError s -> fail s

evalProblem :: String -> [Word64] -> IO [Word64]
evalProblem id args = eval $ EvalProblem id args

evalProgram :: String -> [Word64] -> IO [Word64]
evalProgram program args = eval $ EvalProgram program args

guess :: String -> Program -> IO GuessResponse
guess id p = rpc "guess" $ Guess id $ show p

-- UTILITY

rpc :: (JSON i, JSON o) => String -> i -> IO o
rpc path req = do result <- simpleHTTP $ postRequestWithBody url contentType body
                  case result of
                    Right resp -> case rspCode resp of
                      (2, 0, 0) -> case decode $ rspBody resp of
                        Ok obj -> return obj
                        Error e -> fail e
                      _ -> fail $ rspReason resp
                    Left e -> fail $ show e
  where url = "http://icfpc2013.cloudapp.net/" ++ path ++ "?auth=" ++ auth
        contentType = "application/json"
        body = encode $ showJSON req
          
lookup' :: (Show k, Eq k, JSON a) => k -> [(k, JSValue)] -> Result a
lookup' key = maybe (fail $ "Couldn't find key: " ++ show key) readJSON . lookup key

lookupMaybe :: (Eq k, JSON a) => k -> [(k, JSValue)] -> Result (Maybe a)
lookupMaybe key map = case lookup key map of
                        Just json -> Just `fmap` readJSON json
                        Nothing -> return Nothing

unResult :: (Monad m) => Result a -> m a
unResult (Ok a) = return a
unResult (Error s) = fail s

toHex :: Word64 -> String
toHex = ("0x" ++) . reverse . take 16 . (++ repeat '0') 
        . reverse . map toUpper . (flip showHex "")
