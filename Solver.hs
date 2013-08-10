-- | Attempt to actually solve the problems.

module Solver where

import Debug.Trace ( trace )

import Client
import Program

import Control.Monad ( forM, forM_ )
import Data.Bits ( Bits, (.&.), shiftL, shiftR, shift, xor )
import Data.List ( (\\), delete, groupBy, intercalate, 
                   nub, replicate, sort, sortBy, union )
import Data.Function ( on )
import Data.Maybe ( fromJust )
import Data.Monoid ( Monoid(..) )
import Data.Ord ( comparing )
import Data.Word ( Word64 )
import System.Random ( Random(..), RandomGen(..) )
import System.IO.Unsafe ( unsafeInterleaveIO )
import Text.ParserCombinators.Parsec ( parse )
import Text.Printf ( printf )

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

checkOutputs :: IsProgram p => [Word64] -> [Word64] -> p -> Bool
checkOutputs [] [] _ = True
checkOutputs (i:is) (o:os) p | evaluate p i == o = checkOutputs is os p
                             | otherwise = False

-- countingFilter :: Int -> (a -> Bool) -> [a] -> IO [a]
-- countingFilter incr p list = unsafeInterleaveIO $ cf' 0 0 list
--   where cf' acc rej [] = do putStrLn $ msg " finished" acc rej
--                             return []
--         cf' acc rej (a:as) | p a = do if (acc + 1) `mod` incr == 0
--                                          then putStrLn $ msg "" (acc+1) rej
--                                          else return ()
--                                       (a:) `fmap` cf' (acc+1) rej as
--                            | otherwise = do if (rej + 1) `mod` incr == 0
--                                                then putStrLn $ msg "" acc (rej+1)
--                                                else return ()
--                                             cf' acc (rej+1) as
--         msg m a r = "Filter" ++ m ++ ": accepted " ++ show a ++ 
--                     " and rejected " ++ show r ++ " elements."

solve :: Int -> String -> IO () -- (TrainingProblem, [Word64], [Word64], GuessResponse)
solve n os = do t <- train (Just n) os
                putStrLn $ "Problem id: " ++ trainingId t
                putStrLn $ "Problem size: " ++ show (trainingSize t)
                putStrLn $ "Problem operators: " ++ show (trainingOperators t)
                retry 3 (attempt t ([], [])) (attempt t)
  where attempt t ss = do let (is0, os0) = ss
                          is <- if null is0 
                                then (smallInputs 64 ++) `fmap` pickInputs 190
                                else pickInputs 250
                          os <- evalProblem (trainingId t) is
                          let ps = generate (trainingSize t) (trainingOperators t)
                          -- putStrLn $ "Possible programs: " ++ show (length ps)
                          -- putStrLn "Filtering"
                          let ps' = filter (checkOutputs is os) ps
                          -- putStrLn $ "Filtered programs: " ++ show (length ps')
                          iterate ps' (is0++is) (os0++os)
                            where iterate x is os = do
                                    -- putStrLn "Iterate"
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

tryP :: IsProgram p => [Word64] -> [Word64] -> p -> Int
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

differenceC :: Word64 -> Word64 -> Word64 -> [(Int, Effect)]
differenceC = d' 0
  where d' n _ 0 0 = []
        d' n i' i o | i .&. 1 /= o .&. 1 = (n, if i'.&.1 == o.&.1 then Opposite else Same) 
                                           : d' (n+1) (i'.>>.1) (i.>>.1) (o.>>.1)
                    | otherwise = d' (n+1) (i'.>>.1) (i.>>.1) (o.>>.1)

checkBit :: IsProgram p => p -> Int -> Word64 -> Bool
checkBit p b x = checkBit' p (evaluate p x) b x

-- | partially applied for efficiency so we don't keep checking 0
checkBit' :: IsProgram p => p -> Word64 -> Int -> Word64 -> Bool
checkBit' p x0 b x = evaluate p (flipBit b x) /= x0

data Effect = NoEffect | Same | Opposite | Both
            deriving ( Eq, Enum, Ord )

instance Show Effect where
  show NoEffect = ""
  show Same = "+"
  show Opposite = "-"
  show Both = "?"

instance Monoid Effect where
  mempty = NoEffect
  mappend NoEffect x = x
  mappend x NoEffect = x
  mappend x y | x == y = x
              | otherwise = Both

newtype Correlation = Correlation [(Int, [(Int, Effect)])]

instance Monoid Correlation where
  mempty = Correlation []
  mappend (Correlation a) (Correlation b) = Correlation $ app a b
    where app [] b = b
          app a [] = a
          app (a:as) (b:bs) | fst a == fst b = (fst a, merge (snd a) (snd b)):app as bs
                            | fst a < fst b = a:app as (b:bs)
                            | otherwise = b:app (a:as) bs
          merge [] b = b
          merge a [] = a
          merge (a:as) (b:bs) | fst a == fst b = (fst a, mappend (snd a) (snd b)):merge as bs
                              | fst a < fst b = a:merge as (b:bs)
                              | otherwise = b:merge (a:as) bs

instance Show Correlation where
  show (Correlation rows) = intercalate "\n" $ map s rows
    where s (b, (corr)) = printf "%2d    " b ++ s' Nothing corr
          s' Nothing ((i,b):(i',b'):ss) | i'==i+1 && b==b'
                                         = s' (Just i) ((i',b'):ss)
                                        | otherwise
                                         = s'' (i,b) ++ " " ++ s' Nothing ((i',b'):ss)
          s' Nothing (x:[]) = s'' x
          s' Nothing [] = []
          s' (Just i'') ((i,b):(i',b'):ss) | i'==i+1 && b==b'
                                            = s' (Just i'') ((i',b'):ss)
                                           | otherwise
                                            = s'' (i'',b) ++ ".." ++ show i ++ " " ++ 
                                              s' Nothing ((i',b'):ss)
          s' (Just i') ((i,b):[]) = s'' (i',b) ++ ".." ++ show i
          s'' (i, NoEffect) = ""
          s'' (i, eff) = show eff ++ show i

checkBitsC :: IsProgram p => p -> Word64 -> Correlation
checkBitsC p x = Correlation $
                let y0 = evaluate p x
                in do b <- [0..63]
                      let x1 = flipBit b x
                          y1 = evaluate p x1
                      case differenceC x1 y0 y1 of
                        [] -> fail ""
                        bs -> return (b, bs)


-- (output bit = left edge, input bit = top edge)
newtype Table = Table [((Int, Int), [(Word64, Bool)])]

instance Monoid Table where
  mempty = Table []
  mappend (Table a) (Table b) = Table $ app a b
    where app [] b = b
          app a [] = a
          app (a:as) (b:bs) | fst a == fst b = (fst a, snd a ++ snd b):app as bs
                            | fst a < fst b = a:app as (b:bs)
                            | otherwise = b:app (a:as) bs

instance Show Table where
 show (Table xs) = intercalate "\n" $ header : map showRow rows
    where rows = groupBy ((==) `on` (fst . fst)) xs
          cols :: [Int]
          cols = nub $ sort $ map (snd . fst) xs
          header :: String
          header = "   " ++ concat (map (printf "%3d") cols)
          showRow :: [((Int, Int), [(Word64, Bool)])] -> String
          showRow r = printf "%2d  " (fst $ fst $ head r) ++ terms cols r
          terms :: [Int] -> [((Int, Int), [(a, Bool)])] -> String
          terms [] _ = ""
          terms (c:cs) t@(((_, c'), d):ds) | c == c' = showCell d ++ terms cs ds
                                           | otherwise = "   " ++ terms cs t
          terms (c:cs) [] = ""
          showCell ds = if all snd ds 
                        then " + " else if any (not . snd) ds
                                        then " ~ " else " ? "

differenceT :: Word64 -> Word64 -> Word64 -> [(Int, Bool)]
differenceT ii' = d' 0 ii'
  where d' n _ 0 0 = []
        d' n i' i o | i .&. 1 /= o .&. 1 = (n, i'.&.1 == o.&.1)
                                           : d' (n+1) (i'.>>.1) (i.>>.1) (o.>>.1)
                    | otherwise = d' (n+1) (i'.>>.1) (i.>>.1) (o.>>.1)

checkBits :: IsProgram p => p -> Word64 -> Table
checkBits p x = Table $ sortBy (comparing fst) $
                let y0 = evaluate p x
                in do b <- [0..63]
                      let x1 = flipBit b x
                          y1 = evaluate p x1
                      (c, r) <- differenceT x1 y0 y1
                      return ((c, b), [(x, r)])

-- explore :: [Word64] -> [Word64] -> IO ()
-- explore is os = do forM_ [1..64] $ \n -> do
                     
--                      print $ findOnes $ (i .<<. n) `xor` i `xor` maxBound
                   
