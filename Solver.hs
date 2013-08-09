-- | Attempt to actually solve the problems.

module Solver where

import Debug.Trace ( trace )

import Client
import Program

import Data.List ( (\\), delete, replicate, union )
import Data.Maybe ( fromJust )
import Text.ParserCombinators.Parsec ( parse )

bruteForce :: Problem -> [Program]
bruteForce (Problem _ s o _ _) = do e <- generate ["x"] (s-1) ops ops
                                    return $ P "x" e
  where ops = map (fromJust . parseOp) o

-- Generates a list of all possible programs
generate :: [String] -> Int -> [Op] -> [Op] -> [Expression]
generate vars size needed allowed =
  if TFold `elem` needed
  then foldOnly
  else if CFold `elem` needed
       then foldOnly ++ noFold
       else noFold
  where foldOnly = generateFold vars (size - 2) (unfold needed) (unfold allowed)
        noFold = generate' vars size needed allowed
        unfold = delete TFold . delete CFold

generate' :: [String] -> Int -> [Op] -> [Op] -> [Expression]
generate' vars n rs as 
  | n == 1 && null rs = One : Zero : map Id vars
  | n < 2 = []
  | otherwise = do a <- as
                   case a of
                     Unary o -> do e <- generate vars (n-1) (delete a rs) as
                                   return $ Op1 o e
                     Binary o -> do n1 <- [1..n-2]
                                    let n2 = n-n1-1
                                        rs' = delete a rs
                                    e0 <- generate vars n1 rs' as
                                    e1 <- generate vars n2 (rs' \\ op e0) as
                                    return $ Op2 o e0 e1
                     Cond -> do n1 <- [1..n-3]
                                n2 <- [1..n-2-n1]
                                let n3 = n-n1-n2-1
                                    rs' = delete a rs
                                e0 <- generate vars n1 rs' as
                                let rs'' = rs' \\ op e0
                                e1 <- generate vars n2 rs'' as
                                e2 <- generate vars n3 (rs'' \\ op e1) as
                                return $ If0 e0 e1 e2
                     CFold -> []
                     TFold -> []

generateFold _ _ _ _ = []

-- generate' vars 2 (Unary op:[]) allowed = do e <- generate vars 1 [] allowed
--                                             return $ Op1 op e
-- generate' vars 2 _ _ = []
-- generate' vars 3 required allowed =
--   do a <- allowed
--      case a of
--        Unary op -> do e0 <- generate 
     
  
--   | Just op <- parseOp2 r = do e0 <- generate vars 1 [] allowed
--                                e1 <- generate vars 1 [] allowed
--                                return $ Op2 op e0 e1
--   | Just op <- parseOp1 r = concat [do e0 <- generate vars 2 [r] allowed
--                                        op' <- delete r allowed
--                                        return $ Op1 op' e0,
--                                     do e0 <- generate vars 2 [] allowed
--                                        return $ Op1 op e0]
--   | otherwise = []
-- generate' vars 3 rs 
                               


