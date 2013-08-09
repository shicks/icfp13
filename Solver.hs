-- | Attempt to actually solve the problems.

module Solver where

import Debug.Trace ( trace )

import Client
import Program

import Control.Monad ( forM )
import Data.Bits ( shiftL )
import Data.List ( (\\), delete, replicate, union )
import Data.Maybe ( fromJust )
import Data.Word ( Word64 )
import System.Random ( Random(..), RandomGen(..) )
import Text.ParserCombinators.Parsec ( parse )

generate :: Problem -> [Program]
generate (Problem _ s o _ _) = do e <- generate' ["x"] (s-1) ops ops
                                  return $ P "x" e
  where ops = map (fromJust . parseOp) o

-- Generates a list of all possible programs
generate' :: [String] -> Int -> [Op] -> [Op] -> [Expression]
generate' vars n rs as 
  | n == 1 && null rs = One : Zero : map Id vars
  | n < 2 = []
  | TFold `elem` rs && n >= 5 = fold (delete TFold rs) (delete TFold as)
  | TFold `elem` rs = [] -- not big enough
  | otherwise = do a <- as
                   case a of
                     Unary o -> do e <- generate' vars (n-1) (delete a rs) as
                                   return $ Op1 o e
                     Binary o -> do n1 <- [1..n-2]
                                    let n2 = n-n1-1
                                        rs' = delete a rs
                                    e0 <- generate' vars n1 [] as
                                    e1 <- generate' vars n2 (rs' \\ op e0) as
                                    if e0 <= e1 -- all binops are commutative
                                      then return $ Op2 o e0 e1
                                      else []
                     Cond -> do n1 <- [1..n-3]
                                n2 <- [1..n-n1-2]
                                let n3 = n-n1-n2-1
                                    rs' = delete a rs
                                e0 <- generate' vars n1 [] as
                                let rs'' = rs' \\ op e0
                                e1 <- generate' vars n2 [] as
                                e2 <- generate' vars n3 (rs'' \\ op e1) as
                                return $ If0 e0 e1 e2
                     CFold -> fold (delete CFold rs) (delete CFold as)
  where fold rs' as' = do n1 <- [1..n-4]
                          n2 <- [1..n-n1-3]
                          let n3 = n-n1-n2-2
                          e0 <- generate' vars n1 [] as'
                          let rs'' = rs' \\ op e0 
                          e1 <- generate' vars n2 [] as'
                          e2 <- generate' ("y":"z":vars) n3 (rs'' \\ op e1) as'
                          return $ Fold e0 e1 "y" "z" e2

pickInputs :: Int -> IO [Word64]
pickInputs n = forM [1..n] $ \x -> toWord `fmap` randomRIO (0, (1 `shiftL` 64) - 1)
  where toWord :: Integer -> Word64
        toWord = fromIntegral

checkOutputs :: [Word64] -> [Word64] -> Program -> Bool
checkOutputs [] [] _ = True
checkOutputs (i:is) (o:os) p | evaluate p i == o = checkOutputs is os p
                             | otherwise = False

solve :: Int -> String -> IO (TrainingProblem, [Word64], [Word64], GuessResponse)
solve n os = do t <- train $ TrainRequest (Just n) os
                is <- pickInputs 200
                os <- evalProblem (trainingId t) is
                let ps = generate $ toProblem t
                let ps' = filter (checkOutputs is os) ps
                gr <- if null ps'
                        then return $ GuessError "Empty"
                        else guess (trainingId t) $ head ps'
                return (t, is, os, gr)
