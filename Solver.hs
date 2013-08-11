{-# LANGUAGE TupleSections #-}

-- | Attempt to actually solve the problems.

module Solver where

import Debug.Trace ( trace )

import Client
import Program

import Control.Monad ( forM, forM_ )
import Crypto.Hash.SHA1 ( hash )
import Data.Bits ( Bits, (.&.), (.|.), complement, 
                   shiftL, shiftR, shift, xor )
import Data.ByteString.Lazy ( ByteString )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Base16 as B16
import Data.List ( (\\), delete, elemIndex, groupBy, intercalate, 
                   nub, replicate, sort, sortBy, transpose, union )
import Data.Function ( on )
import Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import Data.Maybe ( catMaybes, fromJust, isJust, listToMaybe )
import qualified Data.MemoCombinators as Memo
import Data.Monoid ( Monoid(..) )
import Data.Ord ( comparing )
import Data.Word ( Word64, Word8 )
import System.Directory ( createDirectoryIfMissing, getDirectoryContents )
import System.Random ( Random(..), RandomGen(..) )
import System.IO.Error ( catchIOError, ioError )
import System.IO.Unsafe ( unsafeInterleaveIO, unsafePerformIO )
import Text.ParserCombinators.Parsec ( parse, eof )
import Text.Printf ( printf )

standardInputs :: [Word64]
standardInputs = nub $ sort $ 0 : complement 0 : small ++ map (`shiftL`16) small ++ 
                 map (\i -> i .|. i `shiftL`32 .|. i `shiftL`48) small ++
                 map complement small ++ 
                 map (\(x,y) -> x .|. (y `shiftL` 25)) 
                     (zip small $ drop 5 small) ++
                 map (\(x,y) -> x `xor` (y `shiftL` 8)) 
                     (zip small $ drop 2 small) ++ allCacheWords
  where small :: [Word64]
        small = [1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 14, 15, 16, 17, 20, 
                 24, 29, 31, 32, 47, 48, 63, 64, 72, 92, 95, 96,
                 127, 128, 192, 255, 256, 511, 512, 1023, 1024, 2047,
                 2048, 32767, 32768, 65535]

generateAll :: [[(Program, [Word64])]]
generateAll = [] : map (\s -> do (e, _, _) <- generateAll' !! (2*s)
                                 let p = P "x" e
                                 return (p, map (evaluate p) standardInputs)) [0..]

generateAll2' :: [[(Int, Int)]]
generateAll2' = concat $ transpose [map (gen' 0) [1..], map (gen' 1) [1..]]
  where gen' v n = replicate n (v, n)

-- Generates a list of all possible programs
        -- TODO - to really benefit here we need the expressions to memoize their values...
generateAll' :: [[(Expression, Bool, Bool)]]
generateAll' = concat $ transpose [map (gen' 0) [1..], map (gen' 1) [1..]]
  where  
    ops = [Unary Not, Unary Shl1, Unary Shr1, Unary Shr4, Unary Shr16,
           Binary Plus, Binary And, Binary Or, Binary Xor, Cond] --, CFold]
    g' v n = generateAll' !! (2*(n-1) + v)
    gen' :: Int -> Int -> [(Expression, Bool, Bool)]
    gen' _ 0 = []
    gen' 0 1 = [(Zero, False, True), (One, False, True), 
                (Id "x", False, False)]
    gen' 1 1 = (Id "y", False, False) : gen' 0 1
    gen' v n = do op <- ops
                  case op of
                       Unary u ->
                         do (e, f, c) <- g' v (n-1)
                            if checkUnary u e 
                              then return $ (Op1 u e, f, c)
                              else []
                       Binary b -> 
                         do n1 <- [1..n-2]
                            let n2 = n-n1-1
                            (e0, f0, c0) <- g' v n1
                            (e1, f1, c1) <- g' v n2
                            if checkBinary b e0 e1 && not (f0 && f1)
                              then return $ 
                                   (Op2 b e0 e1, f0 || f1, c0 && c1)
                              else []
                       Cond -> 
                         do n1 <- [1..n-3]
                            n2 <- [1..n-n1-2]
                            let n3 = n-n1-n2-1
                            (e0, f0, c0) <- g' v n1
                            (e1, f1, c1) <- g' v n2
                            if not (f0 && f1) && not c0 then 
                              do (e2, f2, c2) <- g' v n3
                                 if checkCond e0 e1 e2
                                   then return $ (If0 e0 e1 e2,
                                                  f0 || f1 || f2,
                                                  c0 && c1 && c2)
                                   else []
                              else []
                       CFold ->
                         do n1 <- [1..n-4]
                            n2 <- [1..n-n1-3]
                            let n3 = n-n1-n2-2
                            (e0, False, c0) <- g' v n1
                            (e1, False, c1) <- g' v n2
                            (e2, False, _) <- g' 1 n3
                            return $ (Fold e0 e1 "x" "y" e2, True,
                                      c0 && c1)
    checkUnary Not (Op1 Not _) = False
    checkUnary Shr1 (Op1 Shr4 _) = False  -- commutative
    checkUnary Shr1 (Op1 Shr16 _) = False
    checkUnary Shr4 (Op1 Shr16 _) = False
    checkUnary _ _ = True
    checkBinary b (Op2 b' _ _) _ | b == b' = False -- commutative
    checkBinary b (Op1 Not _) (Op1 Not _) | b /= Plus = False -- factors out
    checkBinary _ e0 e1 | e0 < e1 = False -- commutative
    checkBinary b e0 e1 = checkIndivBinary b e0 && checkIndivBinary b e1
    checkIndivBinary Or Zero = False
    checkIndivBinary And (Op1 Not Zero) = False
    checkIndivBinary Xor Zero = False
    checkIndivBinary Plus Zero = False
    checkIndivBinary _ _ = True
    checkCond _ e0 e1 | e0 == e1 = False
    checkCond _ _ _ = True


generate :: Int -> [String] -> [Program]
generate s o = do e <- generate' ["x"] (s-1) ops ops
                  return $ P "x" e
  where ops = map (fromJust . parseOp) o

-- Generates a list of all possible programs
generate' :: [String] -> Int -> [Op] -> [Op] -> [Expression]
generate' vars n rs as = generate'' vars n rs as
  where 
   generate'' vars n rs as
    | n == 1 && null rs = One : Zero : map Id vars
    | n < 2 = []
    | TFold `elem` rs && n >= 5 = tfold (delete TFold rs) (delete TFold as)
    | TFold `elem` rs = [] -- not big enough
    | otherwise = do 
                   a <- as
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

filterCount :: (a -> Bool) -> [a] -> [(a, Int)]
filterCount = fc 0
  where fc _ _ [] = []
        fc n p (a:as) | p a = (a, n):fc (n+1) p as
                      | otherwise = fc (n+1) p as

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

checkOutputs2 :: [Word64] -> (Program, [Word64]) -> Bool
checkOutputs2 actual (_, memoized) = actual == memoized

lastTrainingProblemRef :: IORef TrainingProblem
lastTrainingProblemRef = unsafePerformIO $ newIORef $ TrainingProblem "" "" 0 []

lastTrainingProblem :: IO TrainingProblem
lastTrainingProblem = readIORef lastTrainingProblemRef

solve2 :: Int -> String -> IO () -- (TrainingProblem, [Word64], [Word64], GuessResponse)
solve2 n os = do t <- train (Just n) os
                 writeIORef lastTrainingProblemRef t
                 putStrLn $ "Problem id: " ++ trainingId t
                 putStrLn $ "Problem size: " ++ show (trainingSize t)
                 putStrLn $ "Problem operators: " ++ show (trainingOperators t)
                 retry 3 (attempt t ()) (attempt t)
  where attempt :: TrainingProblem -> () -> IO (Either () ())
        attempt t _ = do os <- evalProblem (trainingId t) standardInputs
                         let ps = concat $ take 11 generateAll
                         let ps' = filter (checkOutputs2 os) ps
                         iterate $ map fst ps'
                           where iterate x = do
                                    -- putStrLn "Iterate"
                                    (sol:rest) <- return x
                                    response <- guess (trainingId t) sol
                                    -- response <- case x of
                                    --   [] -> fail "Empty"
                                    --   _ -> return ()
                                    case response of
                                      Win -> do putStrLn $ "Theirs: " ++ show (canonicalize $ solution t)
                                                putStrLn $ "Ours: " ++ show sol
                                                return $ Right ()
                                      m@(Mismatch a e _) -> do 
                                        print m
                                        iterate $ filter (checkOutputs [a] [e]) rest
                                      r -> fail $ show r

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

tryAll :: (a -> IO b) -> [a] -> IO b
tryAll f (a:[]) = f a
tryAll f (a:as) = catchIOError (f a) $ \e -> tryAll f as

solveCache :: Show a => (a -> [Word64] -> IO [Word64]) -> (a -> Program -> IO GuessResponse) -> a -> IO ()
solveCache eval guess p = 
              do putStrLn $ "Problem: " ++ show p
                 os <- eval p standardInputs
                 catchIOError (cacheLookups os id) $ \e -> do  -- okay, next guess...?
                   putStrLn "Attempting to recover by adding some reversible operations."
                   tryAll (\(f, t) -> cacheLookups (map (uncurry f) $ zip standardInputs os) t) 
                     reversible
    where cacheLookups :: [Word64] -> (Program -> Program) -> IO ()
          cacheLookups os transf = do 
            probs <- loadCachesFromIO standardInputs os
            let sorted = sortBy (comparing length) probs
            tryAll (doGuess transf . filter (checkOutputs standardInputs os)) sorted
          doGuess :: (Program -> Program) -> [Program] -> IO ()
          doGuess transf x = do
            -- TODO - once we run out, try other options
            case x of
              (sol:rest) -> do
                response <- guess p (transf sol)
                case response of
                  Win -> putStrLn $ "Solved: " ++ show (transf sol)
                  m@(Mismatch a e _) -> do
                    print m
                    doGuess transf $ filter (checkOutputs [a] [e]) rest
                  err -> fail $ show err
              [] -> fail $ "ran out of options"

reversible :: [(Word64 -> Word64 -> Word64, Program -> Program)]
reversible = map reverseXor sp ++ map reversePlus sp
  where sp = -- map unCachedProgram smallPrograms
             map fst $ concat $ take 4 generateAll

reverseXor :: Program -> (Word64 -> Word64 -> Word64, Program -> Program)
reverseXor p = (fix, amend)
  where fix x out = evaluate p x `xor` out
        amend p' = _xor p' p

reversePlus :: Program -> (Word64 -> Word64 -> Word64, Program -> Program)
reversePlus p = (fix, amend)
  where fix x out = evaluate p x - out
        amend p' = _plus p' p

solveCacheTrain :: Maybe Int -> String -> IO ()
solveCacheTrain n os = do t <- train n os
                          putStrLn $ "Problem id: " ++ trainingId t
                          putStrLn $ "Problem size: " ++ show (trainingSize t)
                          putStrLn $ "Problem operators: " ++ show (trainingOperators t)
                          catchIOError (
                            solveCache (\p is -> return $ map (evaluate (solution p)) is) 
                                       (guess . trainingId) t)
                            $ \e -> do writeToAllCaches $ solution t
                                       ioError e
                          

-- is <- if null is0
                 --                then (smallInputs 64 ++) `fmap` pickInputs 190
                 --                else pickInputs 250
                 --          let ps = generate (problemSize p) (problemOperators p)
                 --          -- putStrLn $ "Possible programs: " ++ show (length ps)
                 --          let ps' = filter (checkOutputs is os) ps
                 --          -- putStrLn $ "Filtered programs: " ++ show (length ps')
                 --          iterate ps' (is0++is) (os0++os)
                 --            where iterate x is os = do
                 --                    (sol:rest) <- return x 
                 --                    response <- guess (problemId p) sol
                 --                    -- response <- case x of
                 --                    --   [] -> fail "Empty"
                 --                    --   _ -> return ()
                 --                    case response of
                 --                      Win -> return $ Right ()
                 --                      m@(Mismatch a e _) -> do 
                 --                        print m
                 --                        let rest' = filter (checkOutputs [a] [e]) rest
                 --                        if null rest' then iterate rest' (a:is) (e:os)
                 --                          else return $ Left (a:is, e:os)
                 --                      r -> fail $ show r

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

getBit :: Int -> Word64 -> Bool
getBit b x = (x .&. (1 .<<. b)) /= 0

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
                        then " + " else if not (any snd ds)
                                        then " ~ " else " ? "

differenceT :: Bool -> Word64 -> Word64 -> [(Int, Bool)]
differenceT b = d' 0
  where d' n 0 0 = []
        d' n i o | i .&. 1 /= o .&. 1 = (n, b == (0 /= o.&.1))
                                        : d' (n+1) (i.>>.1) (o.>>.1)
                 | otherwise = d' (n+1) (i.>>.1) (o.>>.1)

checkBits :: IsProgram p => p -> Word64 -> Table
checkBits p x = Table $ sortBy (comparing fst) $
                let y0 = evaluate p x
                in do b <- [0..63]
                      let x1 = flipBit b x
                          y1 = evaluate p x1
                      (c, r) <- differenceT (getBit b x1) y0 y1
                      return ((c, b), [(x, r)])

buildTable :: IsProgram p => p -> IO Table
buildTable p = do is <- pickInputs 100
                  return $ mconcat $ map (checkBits p) (0:is)

-- explore :: [Word64] -> [Word64] -> IO ()
-- explore is os = do forM_ [1..64] $ \n -> do
                     
--                      print $ findOnes $ (i .<<. n) `xor` i `xor` maxBound

cacheLocation :: String
cacheLocation = "cache/"

packForHash :: [Word64] -> [Word8]
packForHash = pfh 0 0
  where pfh 0 _ [] = []
        pfh 0 _ (w:ws) = pfh 8 w ws
        pfh n w ws = fromIntegral (w .&. 255) : pfh (n - 1) (w .>>. 8) ws

-- | A cache is a set of inputs
data Cache = Cache Int [Word64]

-- NOTE: once we start building the cache, this CAN'T CHANGE!
allCaches :: [Cache]
allCaches = [Cache 0 [0, 1, 2, 3, 4, 15, 16, 255, 256, complement 0],
             Cache 1 [0x1234567890abcdef, 0x8877665544332211, 0xf1e2d3c4b5a60798],
             Cache 2 [1.<<.10, 1.<<.40, complement $ 1.<<. 20, complement $ 1 .<<. 50]]

-- extraCaches = allCaches ++ [Cache 3 [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef,
--                                      0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11,
--                                      0xf1, 0xe2, 0xd3, 0xc4, 0xb5, 0xa6, 0x07, 0x98,
--                                      255 - 16, 255 - 4]]

cacheValueLookup :: Word64 -> Maybe (Int, Int)
cacheValueLookup = Memo.integral cvl
  where cvl w = listToMaybe $ catMaybes $
                map (\(i, (Cache _ ws)) -> (i,) `fmap` elemIndex w ws) (zip [0..] allCaches)

allCacheWords = concatMap (\(Cache _ ws) -> ws) allCaches

-- | Writes a program to a cache
writeProgram :: Int       -- ^ Which cache to write to 
             -> Program   -- ^ Program to write 
             -> [Word64]  -- ^ A list of results, will be hashed
             -> IO ()
writeProgram c p os = let h = BC.unpack $ B16.encode $ hash $ BS.pack $ packForHash os
                          dir = concat [cacheLocation, show c, "/", take 3 h]
                          fname = concat [dir, "/", drop 3 h]
                      in do createDirectoryIfMissing True dir
                            appendFile fname $ show p ++ "\n"

checkSame :: Program -> Program -> IO Bool
checkSame p1 p2 = do is <- pickInputs 100
                     let os1 = map (evaluate p1) is
                     let os2 = map (evaluate p2) is
                     return $ os1 == os2

writeToOneCache :: Cache -> Program -> IO ()
writeToOneCache (Cache c is) p = writeProgram c p' $ map (evaluate p') is
  where p' = canonicalize p

writeToAllCaches :: Program -> IO ()
writeToAllCaches p = forM_ allCaches $ 
                        \(Cache c is) -> writeProgram c p' $ map (evaluate p') is
  where p' = canonicalize p

-- given input/output pairs that includes the cache's keys
loadCachesFromIO :: [Word64] -> [Word64] -> IO [[Program]]
loadCachesFromIO ins outs = mapM (\(Cache c cins) -> load' c cins) allCaches
  where load' c cins = let couts = map (\i -> (outs !!) `fmap` elemIndex i ins) cins
                       in if all isJust couts
                          then loadCache c $ map fromJust couts
                          else return []

loadCache :: Int -> [Word64] -> IO [Program]
loadCache c os = let h = BC.unpack $ B16.encode $ hash $ BS.pack $ packForHash os
                     fname = concat [cacheLocation, show c, "/", take 3 h, "/", drop 3 h]
                 in readCacheFile fname

readCacheFile :: FilePath -> IO [Program]
readCacheFile fname = catchIOError ((concatMap readProgram . lines) `fmap` readFile fname) $
                      \e -> return []
  where readProgram :: String -> [Program]
        readProgram s = case parse (do { p <- parseProgram; eof; return p }) "" s of
          Right p -> [p]
          Left _ -> []

loadAll :: Int -> IO [Program]
loadAll c = let dir = cacheLocation ++ show c
            in getDirectoryContents dir >>= fmap concat . mapM (loadPrefix dir)
  where loadPrefix :: FilePath -> FilePath -> IO [Program]
        loadPrefix dir prefix 
          | length prefix == 3 = let subdir = concat [dir, "/", prefix]
                                 in getDirectoryContents subdir >>= fmap concat . mapM (loadDir subdir)
          | otherwise = return []
        loadDir :: FilePath -> FilePath -> IO [Program]
        loadDir dir file 
          | length file > 3 = readCacheFile $ concat [dir, "/", file]
          | otherwise = return []


-- DEPTH FIRST SEARCH
-- We have several parameters:
--  1. Final depth
--  2. Size of binop groups
--  3. Size and style of conditional/fold groups

type EvalF = (Word64, Word64) -> Word64

evalF :: Program -> EvalF
evalF p | size p > 3 = Memo.pair Memo.integral Memo.integral $
                       \(x, y) -> evaluateNamed [("x", x), ("y", y)] p
        | otherwise = \(x, y) -> evaluateNamed [("x", x), ("y", y)] p

data CachedProgram = CachedProgram Program [[Word64]] Bool Bool EvalF -- results, has fold, const
cachedProgram p ws f c = CachedProgram p ws f c (evalF p)

instance Eq CachedProgram where
  (==) (CachedProgram p _ _ _ _) (CachedProgram p' _ _ _ _) = p == p'

instance Ord CachedProgram where
  compare (CachedProgram p _ _ _ _) (CachedProgram p' _ _ _ _) = compare p p'

instance Show CachedProgram where
  show (CachedProgram p _ _ _ _) = show p

writeCachedProgram :: CachedProgram -> IO ()
writeCachedProgram (CachedProgram p os _ _ _) = mapM_ (\(c, o) -> writeProgram c p o) $ 
                                                zip (map cacheNum allCaches) os
  where cacheNum (Cache c _) = c

unCachedProgram :: CachedProgram -> Program
unCachedProgram (CachedProgram p _ _ _ _) = p

-- only needs to work for small programs - no folds
cacheProgram :: Program -> CachedProgram
cacheProgram p = cachedProgram p os False (all (== head (concat os)) $ concat os)
  where os = map (\(Cache c is) -> map (evaluate p) is) allCaches

instance IsProgram CachedProgram where
  evaluate (CachedProgram p ws _ _ _) w = case cacheValueLookup w of
                                            Just (i, j) -> ws !! i !! j
                                            Nothing -> evaluate p w
  evaluateNamed ((_, w):[]) (CachedProgram _ _ _ _ evalf) = evalf (w, 0)
  evaluateNamed (("x", x):("y", y):_) (CachedProgram _ _ _ _ evalf) = evalf (x, y)
  evaluateNamed v (CachedProgram p _ _ _ _) = evaluateNamed v p

instance ProgramBuilder CachedProgram where
  build0 = cachedProgram _0 (map (\(Cache _ is) -> map (const 0) is) allCaches) False True
  build1 = cachedProgram _1 (map (\(Cache _ is) -> map (const 1) is) allCaches) False True
  buildVar v = cachedProgram (buildVar v) (map (\(Cache _ is) -> map id is) allCaches) False True
  buildUnary op (CachedProgram p os f c _) = 
    cachedProgram (buildUnary op p) ((map . map) (op1 op) os) f c
  buildBinary op (CachedProgram p1 os1 f1 c1 _) (CachedProgram p2 os2 f2 c2 _) =
    cachedProgram (buildBinary op p1 p2) (mapBinary op os1 os2) (f1 || f2) (c1 && c2)
    where mapBinary op x1 x2 = map (\(y1,y2) -> map (\(z1,z2) -> op2 op z1 z2) (zip y1 y2)) (zip x1 x2)
  buildCond (CachedProgram p1 os1 f1 c1 _) (CachedProgram p2 os2 f2 c2 _) (CachedProgram p3 os3 f3 c3 _) =
    cachedProgram (buildCond p1 p2 p3) (mapCond os1 os2 os3) (f1 || f2 || f3) (c1 && c2 && c3)
    where mapCond x1 x2 x3 = map (\(y1,y2,y3) -> 
                                   map (\(c,t,f) -> 
                                         if c == 0 then t else f) (zip3 y1 y2 y3)) (zip3 x1 x2 x3)
  buildFold (CachedProgram p1 os1 _ c1 _) (CachedProgram p2 os2 _ c2 _) (CachedProgram p3 os3 _ _ ef) =
    cachedProgram (buildFold p1 p2 p3) (mapFold p3 os1 os2) True (c1 && c2)
    where mapFold p3 x1 x2 = map (\(y1,y2) -> 
                                   map (\(z1,z2) -> evFold z1 z2) (zip y1 y2)) (zip x1 x2)
          evFold x y = foldr (\xv yv -> ef (xv, yv)) y $ reverse $ bytes x


-- maxDepth = 9 -- 9 gets 6 million in 210 sec
-- maxArgSize = 3

-- depth 6 fetched in .5 sec but wrote 90M (22k progs) in 30 secs
--  -> factor of 60 for writing to disk

--smallPrograms = map cacheProgram $ map fst $ concat $ take maxArgSize generateAll
--smallerPrograms = map cacheProgram $ map fst $ concat $ take 3 generateAll

smallPrograms = map cacheProgram [_0, _1, _x, _not _0, _not _1, _not _x, _shl1 _1, 
                                  _shl1 _x, _shr1 _x, _shr4 _x, _shr16 _x]
smallerPrograms = map cacheProgram [_0, _1, _x]

-- data DFTerm = DFZero | DFOne | DFVar | DFUnary Op1 | DFBinary Op2 | DFCond Int | DFFold Int
--             deriving ( Eq, Ord, Show )

-- dfTerms :: [DFTerm]
-- dfTerms = [DFZero, DFOne, DFVar, 
--            DFUnary Not, DFUnary Shl1, DFUnary Shr1, DFUnary Shr4, DFUnary Shr16,
--            DFBinary And, DFBinary Or, DFBinary Xor, DFBinary Plus, 
                  --            DFCond 0, DFCond 1, DFFold 0, DFFold 1]

-- dfDecompose :: Maybe Program -> [DFTerm]
-- dfDecompose Nothing = []
-- dfDecompose Just (P _ e) = reverse $ decomp e
--  where decomp Zero = [DFZero]
--        decomp One = [DFOne]
--        decomp (Id _) = [DFVar]
--        decomp (Op1 op r) = DFUnary op : decomp r
--        decomp (Op2 op r _) = DFBinary op : decomp r
--        decomp (If0 r1 r2 _) = DFCond : decomp 

-- no token - just don't crash...

-- Produce a list of programs
depthFirst :: Int -> [CachedProgram]
depthFirst maxDepth = df _0 ++ df _1 ++ df _x
  where df :: CachedProgram -> [CachedProgram]
        df p | size (unCachedProgram p) >= maxDepth = [p]
             | otherwise = concatMap (addUnary p) [Not, Shl1, Shr1, Shr4, Shr16] ++
                           concatMap (addBinary p) [And, Or, Xor, Plus] ++
                           addCond p ++ addFold p
        addUnary p@(CachedProgram (P _ e) _ _ _ _) op = 
             if checkUnary op e then df (buildUnary op p) else []
        addBinary p@(CachedProgram (P _ e) _ _ _ _) op = 
             concatMap (\p'@(CachedProgram (P _ e') _ _ _ _) -> 
                         if checkBinary op e e' 
                         then df (buildBinary op p p')
                         else []) $ smallPrograms
        addCond p =
             let args = nub $ sort $ concat $ concat [
                   [if checkCond p p1 p2 then [(p, p1, p2)]
                    else [] | p1 <- smallerPrograms, p2 <- smallerPrograms],
                   [if checkCond p1 p p2 then [(p1, p, p2)]
                    else [] | p1 <- smallerPrograms, p2 <- smallerPrograms],
                   [if checkCond p1 p2 p then [(p1, p2, p)] 
                    else [] | p1 <- smallerPrograms, p2 <- smallerPrograms]]
             in concatMap (\(c, t, f) -> df $ _if0 c t f) args
        addFold p@(CachedProgram _ _ f _ _) | f = []
                                            | otherwise =
             let args = nub $ sort $ concat $ concat [
                   [if checkFold p p1 p2 then [(p, p1, p2)]
                    else [] | p1 <- smallerPrograms, p2 <- concatMap shuffleVars smallerPrograms],
                   [if checkCond p1 p p2 then [(p1, p, p2)]
                    else [] | p1 <- smallerPrograms, p2 <- concatMap shuffleVars smallerPrograms],
                   [if checkCond p1 p2 p then [(p1, p2, p')] 
                    else [] | p' <- shuffleVars p, p1 <- smallerPrograms, p2 <- smallerPrograms]]
             in concatMap (\(e0, e1, e2) -> df $ _fold e0 e1 e2) args
        checkUnary Not (Op1 Not _) = False
        checkUnary Shr1 (Op1 Shr4 _) = False  -- commutative
        checkUnary Shr1 (Op1 Shr16 _) = False
        checkUnary Shr4 (Op1 Shr16 _) = False
        checkUnary Shl1 Zero = False
        checkUnary Shr1 Zero = False
        checkUnary Shr4 Zero = False
        checkUnary Shr16 Zero = False
        checkUnary Shr1 One = False
        checkUnary Shr4 One = False
        checkUnary Shr16 One = False
        checkUnary _ _ = True
        -- checkBinary b (Op2 b' _ _) _ | b == b' = False -- commutative
        checkBinary b (Op1 Not _) (Op1 Not _) | b /= Plus = False -- factors out
        checkBinary b e0 e1 | b /= Plus && e0 == e1 = False -- x or x is boring
                            | size e0 < size e1 || (size e0 == size e1 && e0 < e1) = False -- commutative
                            | otherwise = checkIndivBinary b e0 && checkIndivBinary b e1
        checkIndivBinary Or Zero = False
        checkIndivBinary Or (Op1 Not Zero) = False
        checkIndivBinary And Zero = False
        checkIndivBinary And (Op1 Not Zero) = False
        checkIndivBinary Xor Zero = False
        checkIndivBinary Plus Zero = False
        checkIndivBinary _ _ = True
        checkCond (CachedProgram _ _ _ True _) _ _ = False
        checkCond _ t f | t == f = False
        checkCond _ _ _ = True
        checkFold _ _ _ = True
        shuffleVars :: CachedProgram -> [CachedProgram]
        shuffleVars (CachedProgram (P v e) _ _ _ _) = map (\e' -> cachedProgram (P v e') [] False False)
                                                      (sv e)
          where sv Zero = [Zero]
                sv One = [One]
                sv (Id _) = [Id "x", Id "y"]
                sv (Op1 op e) = map (Op1 op) $ sv e
                sv (Op2 op e1 e2) = [Op2 op e1' e2' | e1' <- sv e1, e2' <- sv e2]
                sv (If0 c t f) = [If0 c' t' f' | c' <- sv c, t' <- sv t, f' <- sv f]
                sv e = [e]
