-- | Attempt to actually solve the problems.

module Solver where

import Debug.Trace ( trace )

import Client
import Program

import Control.Monad ( forM, forM_ )
import Data.Bits ( Bits, (.&.), shiftL, shiftR, shift, xor )
import Data.List ( (\\), delete, replicate, sortBy, union )
import Data.Maybe ( fromJust )
import Data.Ord ( comparing )
import Data.Word ( Word64 )
import System.Random ( Random(..), RandomGen(..) )
import Text.ParserCombinators.Parsec ( parse )

generate :: Int -> [String] -> [Program]
generate s o = do e <- generate' ["x"] (s-1) ops ops
                  return $ P "x" e
  where ops = map (fromJust . parseOp) o

-- Generates a list of all possible programs
generate' :: [String] -> Int -> [Op] -> [Op] -> [Expression]
generate' vars n rs as 
  | n == 1 && null rs = One : Zero : map Id vars
  | n < 2 = []
  | TFold `elem` rs && n >= 5 = tfold (delete TFold rs) (delete TFold as)
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
                          e2 <- generate' ("y":"z":[] {-vars-}) n3 (rs'' \\ op e1) as'
                          return $ Fold e0 e1 "y" "z" e2
        tfold rs' as' = do let n3 = n-4
                               e0 = Id "x"
                               e1 = Zero
                           e2 <- generate' ("y":"z":[] {-vars-}) n3 rs' as'
                           return $ Fold e0 e1 "y" "z" e2

pickInputs :: Int -> IO [Word64]
pickInputs n = forM [1..n] $ \x -> toWord `fmap` randomRIO (0, (1 `shiftL` 64) - 1)
  where toWord :: Integer -> Word64
        toWord = fromIntegral

smallInputs :: Int -> [Word64]
smallInputs n = [0..fromIntegral n]

checkOutputs :: [Word64] -> [Word64] -> Program -> Bool
checkOutputs [] [] _ = True
checkOutputs (i:is) (o:os) p | evaluate p i == o = checkOutputs is os p
                             | otherwise = False

solve :: Int -> String -> IO () -- (TrainingProblem, [Word64], [Word64], GuessResponse)
solve n os = do t <- train (Just n) os
                putStrLn $ "Problem id: " ++ trainingId t
                putStrLn $ "Problem size: " ++ show (trainingSize t)
                putStrLn $ "Problem operators: " ++ show (trainingOperators t)
                retry 3 (attempt t []) (attempt t)
  where attempt t ss = do is <- (\x -> ss ++ smallInputs 64 ++ x) `fmap` pickInputs 136
                          os <- evalProblem (trainingId t) is
                          let ps = generate (trainingSize t) (trainingOperators t)
                          -- putStrLn $ "Possible programs: " ++ show (length ps)
                          let ps' = filter (checkOutputs is os) ps
                          -- putStrLn $ "Filtered programs: " ++ show (length ps')
                          iterate ps' (is0++is) (os0++os)
                            where iterate x is os = do
                                    (sol:rest) <- return x 
                                    response <- guess (trainingId t) sol
                                    -- response <- case x of
                                    --   [] -> fail "Empty"
                                    --   _ -> return ()
                                    case response of
                                      Win -> return $ Right ()
                                      m@(Mismatch a e _) -> do 
                                        print m
                                        let rest' = filter (checkOutputs [a] [e]) rest
                                        if null rest' then iterate rest' (a:is) (e:os)
                                          else return $ Left (a:is, e:os)
                                      r -> fail $ show r
                          
                          
                          -- response <- case ps' of
                          --   (sol:_) -> guess (trainingId t) sol
                          --   [] -> fail "Empty"
                          -- case response of
                          --   Win -> return $ Right ()
                          --   m@(Mismatch a _ _) -> do print m 
                          --                            return $ Left $ a:ss
                          --   r -> fail $ show r

                -- gr <- case ps' of
                --   (p:_) -> guess (trainingId t) p
                --   []    -> return $ GuessError "Empty"
                -- return (t, is, os, gr)

solveReal :: Problem -> IO ()
solveReal p = do putStrLn $ "Problem: " ++ show p
                 retry 3 (attempt p ([], [])) (attempt p)
  where attempt p ss = do let (is0, os0) = ss
                          is <- if null is0 
                                then (smallInputs 64 ++) `fmap` pickInputs 190
                                else pickInputs 250
                          os <- evalProblem (problemId p) is
                          let ps = generate (problemSize p) (problemOperators p)
                          -- putStrLn $ "Possible programs: " ++ show (length ps)
                          let ps' = filter (checkOutputs is os) ps
                          -- putStrLn $ "Filtered programs: " ++ show (length ps')
                          iterate ps' (is0++is) (os0++os)
                            where iterate x is os = do
                                    (sol:rest) <- return x 
                                    response <- guess (problemId p) sol
                                    -- response <- case x of
                                    --   [] -> fail "Empty"
                                    --   _ -> return ()
                                    case response of
                                      Win -> return $ Right ()
                                      m@(Mismatch a e _) -> do 
                                        print m
                                        let rest' = filter (checkOutputs [a] [e]) rest
                                        if null rest' then iterate rest' (a:is) (e:os)
                                          else return $ Left (a:is, e:os)
                                      r -> fail $ show r

-- How would we solve something by hand?
-- 1. what sequence of bits are in common?
-- 2. what pair of sequences can be xor'd/and'd/or'd to be in common?
-- 3. what bits are missing ?
-- 4. prefer longer runs?

-- What kind of output is it producing?  Are there any higher-order bits at all?


(.<<.), (.>>.) :: (Bits a) => a -> Int -> a
(.<<.) = shiftL
(.>>.) = shiftR
for = flip map

findOnes :: Word64 -> [Int]
findOnes = findOnes' 0
  where findOnes' _ 0 = []
        findOnes' n x | x .&. 1 == 1 = n:findOnes' (n+1) (x.>>.1)
                      | otherwise = findOnes' (n+1) (x.>>.1)

proximity :: Word64 -> Word64 -> Int
proximity a b = 64 - length (findOnes $ a `xor` b `xor` 1)

tryP :: [Word64] -> [Word64] -> Program -> Int
tryP is os p = sum $ map (\(i, o) -> proximity (evaluate p i) o) $ zip is os

maybeNot :: [Expression -> Expression]
maybeNot = [id, Op1 Not]

explore :: [Word64] -> [Word64] -> [(Program, Int)]
explore is os = reverse $ sortBy (comparing snd) $ explore 1
  where opt :: Expression -> (Program, Int)
        opt e = let p = P "x" e in (p, tryP is os p)
        x :: Expression
        x = Id "x"
        explore :: Int -> [(Program, Int)]
        explore 1 = do n <- [-63..63]
                       return $ opt $ Shift n x
        explore 2 = do n <- [-63..63]
                       m <- [-63..63]
                       op <- [And, Or, Xor, Plus]
                       return $ opt $ Op2 op (Shift n x) (Shift m x)

flipBit :: Int -> Word64 -> Word64
flipBit b x = x `xor` (1 .<<. b)

difference :: Word64 -> Word64 -> [Int]
difference = d' 0
  where d' n 0 0 = []
        d' n i o | i .&. 1 /= o .&. 1 = n : d' (n+1) (i.>>.1) (o.>>.1)
                 | otherwise = d' (n+1) (i.>>.1) (o.>>.1)

checkBit :: Program -> Int -> Word64 -> Bool
checkBit p b x = checkBit' p (evaluate p x) b x

-- | partially applied for efficiency so we don't keep checking 0
checkBit' :: Program -> Word64 -> Int -> Word64 -> Bool
checkBit' p x0 b x = evaluate p (flipBit b x) /= x0

checkBits :: Program -> Word64 -> [(Int, [Int])]
checkBits p x = let y0 = evaluate p x
                in do b <- [0..63]
                      let y1 = evaluate p (flipBit b x)
                      case difference y0 y1 of
                        [] -> fail ""
                        bs -> return (b, bs)

-- explore :: [Word64] -> [Word64] -> IO ()
-- explore is os = do forM_ [1..64] $ \n -> do
                     
--                      print $ findOnes $ (i .<<. n) `xor` i `xor` maxBound
                   
