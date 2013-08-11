{-# LANGUAGE TupleSections, ViewPatterns #-}

module Program where

import Data.Bits ( (.&.), (.|.), complement, shift, shiftL, shiftR, xor )
import Data.Char ( ord, toLower )
import Data.List ( nub, sort )
import Data.Maybe ( fromJust )
import Data.Word ( Word64 )
import Text.ParserCombinators.Parsec ( Parser, (<|>), oneOf,
                                       char, choice, digit, eof, letter,
                                       many, many1, parse, spaces,
                                       string, try, getPosition,
                                       sourceColumn )

class IsProgram p where
  evaluate :: p -> Word64 -> Word64
  evaluateNamed :: [(String, Word64)] -> p -> Word64

data Program = P { param :: String, unP ::  Expression }
             deriving ( Eq, Ord )
data Expression = Zero | One | Id String
                | If0 Expression Expression Expression
                | Fold Expression Expression String String Expression
                | Op1 Op1 Expression
                | Op2 Op2 Expression Expression
                | Shift Int Expression
                | Const Word64
                deriving ( Eq, Ord )
data Op1 = Not | Shl1 | Shr1 | Shr4 | Shr16
         deriving ( Bounded, Eq, Enum, Ord )
data Op2 = And | Or | Xor | Plus
         deriving ( Bounded, Eq, Enum, Ord )

data Op = Cond | CFold | TFold | Unary Op1 | Binary Op2
        deriving ( Eq, Ord )

class ProgramBuilder p where
  build0 :: p
  build1 :: p
  buildVar :: String -> p
  buildUnary :: Op1 -> p -> p
  buildBinary :: Op2 -> p -> p -> p
  buildCond :: p -> p -> p -> p
  buildFold :: p -> p -> p -> p

instance ProgramBuilder Program where
  build0 = P "x" Zero
  build1 = P "x" One
  buildVar s = P "x" $ Id s
  buildUnary op (P v x) = P v $ Op1 op x
  buildBinary op (P v x) (P _ y) = P v $ Op2 op x y
  buildCond (P v c) (P _ t) (P _ f) = P v $ If0 c t f
  buildFold (P v e0) (P _ e1) (P _ e2) = P v $ Fold e0 e1 "x" "y" e2

_0, _1, _x, _y :: ProgramBuilder p => p
_0 = build0
_1 = build1
_x = buildVar "x"
_y = buildVar "y"
_not, _shr1, _shr4, _shr16, _shl1 :: ProgramBuilder p => p -> p
_not = buildUnary Not
_shr1 = buildUnary Shr1
_shr4 = buildUnary Shr4
_shr16 = buildUnary Shr16
_shl1 = buildUnary Shl1
_and, _or, _xor, _plus :: ProgramBuilder p => p -> p -> p
_and = buildBinary And
_or = buildBinary Or
_xor = buildBinary Xor
_plus = buildBinary Plus
_if0, _fold :: ProgramBuilder p => p -> p -> p -> p
_if0 = buildCond
_fold = buildFold
_tfold :: ProgramBuilder p => p -> p
_tfold z = _fold _x _0 z

instance Show Program where
  show (P s e) = "(lambda (" ++ s ++ ") " ++ show e ++ ")"

instance Show Expression where
  show Zero = "0"
  show One = "1"
  show (Id s) = s
  show (If0 c t f) = "(if0 " ++ show c ++ " " ++ show t ++ " " ++ show f ++ ")"
  show (Fold arg start x y e) = concat ["(fold ", show arg, " ", show start,
                                        " (lambda (", x, " ", y, ") ", show e, "))"]
  show (Op1 op e) = "(" ++ show op ++ " " ++ show e ++ ")"
  show (Op2 op e0 e1) = "(" ++ show op ++ " " ++ show e0 ++ " " ++ show e1 ++ ")"
  show (Shift n e) = "(shift " ++ show n ++ " " ++ show e ++ ")"
  show (Const x) = show x

instance Show Op1 where
  show op = fromJust $ lookup op [(Not, "not"), (Shl1, "shl1"), (Shr1, "shr1"), 
                                  (Shr4, "shr4"), (Shr16, "shr16")]

instance Show Op2 where
  show op = fromJust $ lookup op [(And, "and"), (Or, "or"),
                                  (Xor, "xor"), (Plus, "plus")]

instance Show Op where
  show Cond = "if0"
  show TFold = "tfold"
  show CFold = "fold"
  show (Unary op) = show op
  show (Binary op) = show op

instance Read Program where
  readsPrec _ s = case parse (do p <- parseProgram    -- arrows?
                                 pos <- getPosition
                                 return (pos, p)) "" s of
                    Right (pos, p) -> [(p, drop (sourceColumn pos - 1) s)]
                    Left err -> error $ show err

bytes :: Word64 -> [Word64]
bytes = take 8 . drop 1 . map fst . iterate next . (0,)
  where next (a, b) = (b .&. 0xff, b `shiftR` 8)

instance IsProgram Program where
  evaluate (P s e) x = evaluateNamed [(s, x)] e
  evaluateNamed v (P s e) = evaluateNamed v e

evalFold :: IsProgram p => p -> Word64 -> Word64 -> Word64
evalFold p x y = foldr (\xv yv -> evaluateNamed [("x", xv), ("y", yv)] p) y $ reverse $ bytes x

instance IsProgram Expression where
  evaluate e x = evaluateNamed [("x", x)] e

  evaluateNamed _ Zero = 0
  evaluateNamed _ One = 1
  evaluateNamed v (Id s') = case lookup s' v of
    Just x  -> x
    Nothing -> error $ "Looked for " ++ s' ++ " but only had " ++ show v
  evaluateNamed v (If0 c t f) = if evaluateNamed v c == 0 
                                then evaluateNamed v t 
                                else evaluateNamed v f
  evaluateNamed v (Fold arg start sy sz accum) = foldr f (evaluateNamed v start) $ 
                                                 reverse $ bytes $ evaluateNamed v arg
    where f y z = evaluateNamed ((sy, y):(sz, z):v) accum
  evaluateNamed v (Op1 op e) = op1 op $ evaluateNamed v e
  evaluateNamed v (Op2 op y z) = op2 op (evaluateNamed v y) (evaluateNamed v z)
  evaluateNamed v (Shift n e) = shift (evaluateNamed v e) n
  evaluateNamed _ (Const x) = x

op1 :: Op1 -> Word64 -> Word64
op1 Not = complement
op1 Shl1 = flip shiftL 1
op1 Shr1 = flip shiftR 1
op1 Shr4 = flip shiftR 4
op1 Shr16 = flip shiftR 16

op2 :: Op2 -> Word64 -> Word64 -> Word64
op2 And = (.&.)
op2 Or = (.|.)
op2 Xor = xor
op2 Plus = (+)

class HasSize s where
  size :: s -> Int

instance HasSize Program where
  size (P _ e) = 1 + size e

instance HasSize Expression where
  size Zero = 1
  size One = 1
  size (Id _) = 1
  size (If0 c t f) = 1 + size c + size t + size f
  size (Fold e0 e1 _ _ e2) = 2 + size e0 + size e1 + size e2
  size (Op1 _ e) = 1 + size e
  size (Op2 _ e0 e1) = 1 + size e0 + size e1

op :: Expression -> [Op]
op = nub . sort . op'
  where op' Zero = []
        op' One = []
        op' (Id _) = []
        op' (If0 c t f) = Cond : op' c ++ op' t ++ op' f
        op' (Fold e0 e1 _ _ e2) = CFold : op' e0 ++ op' e1 ++ op' e2
        op' (Op1 op e) = Unary op : op' e
        op' (Op2 op e0 e1) = Binary op : op' e0 ++ op' e1

-- | Note: in the spec this is described as a binary relation, but
-- it seems like the second argument is strictly dependent on the
-- first, so I'm implementing it as a function.
operators :: Program -> [Op]
operators (P _ (Fold e0 e1 _ _ e2)) = nub $ sort $ TFold : op e0 ++ op e1 ++ op e2
operators (P _ e) = op e

parseProgram :: Parser Program
parseProgram = do string "(" >> spaces
                  string "lambda" >> spaces
                  string "(" >> spaces
                  s <- word
                  spaces >> string ")" >> spaces
                  e <- parseExpr
                  spaces >> string ")"
                  return $ P s e

parseExpr :: Parser Expression
parseExpr = choice $ map try $ [string "0" >> return Zero,
                                string "1" >> return One,
                                Id `fmap` word,
                                do string "(" >> spaces >> string "if0"
                                   c <- spaces >> parseExpr
                                   t <- spaces >> parseExpr
                                   f <- spaces >> parseExpr
                                   spaces >> string ")"
                                   return $ If0 c t f,
                                do string "(" >> spaces >> string "fold"
                                   e0 <- spaces >> parseExpr
                                   e1 <- spaces >> parseExpr
                                   spaces >> string "(" >> spaces
                                   string "lambda" >> spaces >> string "("
                                   id0 <- spaces >> word
                                   id1 <- spaces >> word
                                   spaces >> string ")"
                                   e2 <- spaces >> parseExpr
                                   spaces >> string ")" >> spaces >> string ")"
                                   return $ Fold e0 e1 id0 id1 e2,
                                do string "(" >> spaces
                                   op <- parseEnum
                                   e <- spaces >> parseExpr
                                   spaces >> string ")"
                                   return $ Op1 op e,
                                do string "(" >> spaces
                                   op <- parseEnum
                                   e0 <- spaces >> parseExpr
                                   e1 <- spaces >> parseExpr
                                   spaces >> string ")"
                                   return $ Op2 op e0 e1,
                                do string "(" >> spaces >> string "shift"
                                   n <- spaces >> number
                                   e <- spaces >> parseExpr
                                   spaces >> string ")"
                                   return $ Shift n e]

allEnums :: (Bounded a, Enum a) => [a]
allEnums = [minBound .. maxBound]

word :: Parser String
word = do c <- letter <|> char '_'
          cs <- many $ letter <|> digit <|> char '_'
          return $ c:cs

number :: Num a => Parser a
number = choice [do char '-' 
                    n <- number
                    return $ -n,
                 try $ do string "0x"
                          ds <- many1 hexDigit
                          return $ foldr (\a b -> 16 * b + a) 0 $ reverse ds,
                 try $ do ds <- many1 decDigit
                          return $ foldr (\a b -> 10 * b + a) 0 $ reverse ds]

hexDigit :: Num a => Parser a
hexDigit = fromIntegral `fmap` 
           choice [decDigit,
                   fmap (\x -> ord x - ord 'A' + 10) $ oneOf "ABCDEF",
                   fmap (\x -> ord x - ord 'a' + 10) $ oneOf "abcdef"]

decDigit :: Num a => Parser a
decDigit = fromIntegral `fmap` fmap (\x -> ord x - ord '0') digit

parseNum :: Num a => String -> Either String a
parseNum s = case parse number "" s of Right n -> Right n
                                       Left e -> Left $ show e

parseEnum :: (Bounded a, Enum a, Show a) => Parser a
parseEnum = try $ do w <- word
                     (a:[]) <- return $ filter ((==w) . show) allEnums
                     return a

parseOp :: String -> Maybe Op
parseOp s = lookup s [("not", Unary Not), ("shl1", Unary Shl1),
                      ("shr1", Unary Shr1), ("shr4", Unary Shr4),
                      ("shr16", Unary Shr16), ("and", Binary And),
                      ("or", Binary Or), ("xor", Binary Xor),
                      ("plus", Binary Plus), ("if0", Cond),
                      ("fold", CFold), ("tfold", TFold)]

isConst :: Expression -> Maybe Word64
isConst e = if ic e
            then Just $ evaluate (P "x" e) 0 
            else Nothing
  where ic Zero = True
        ic One = True
        ic (Const _) = True
        ic (Id _) = False
        ic (Op1 _ e) = ic e
        ic (Shift _ e) = ic e
        ic (Op2 _ e0 e1) = ic e0 && ic e1
        ic (If0 c t f) | Just x <- isConst c = if x == 0 then ic t else ic f
                       | Just x <- isConst t = t == f
                       | otherwise = False
        ic (Fold e0 e1 x y e2) = ic e0 && ic e1

canonicalize :: Program -> Program
canonicalize (P s e) = P "x" $ c' [(s, "x")] e
  where c' _ One = One
        c' _ Zero = Zero
        c' v (Id x) = Id $ maybe x id $ lookup x v
        c' v (Op1 op e) = Op1 op (c' v e)
        c' v (Op2 op e0 e1) = Op2 op (c' v e0) (c' v e1)
        c' v (If0 c t f) = If0 (c' v c) (c' v t) (c' v f)
        c' v (Fold e0 e1 x y e2) = Fold (c' v e0) (c' v e1) "x" "y" 
                                   (c' ((x,"x"):(y,"y"):v) e2)
        c' v (Shift 0 e) = c' v e
        c' v (Shift n e) | n > 0 = Op1 Shl1 (c' v (Shift (n-1) e))
        c' v (Shift n e) | n <= -16 = Op1 Shr16 (c' v (Shift (n+16) e))
        c' v (Shift n e) | n <= -4 = Op1 Shr4 (c' v (Shift (n+4) e))
        c' v (Shift n e) | n < 0 = Op1 Shr1 (c' v (Shift (n+1) e))
        c' _ (Const 0) = Zero
        c' _ (Const 1) = One
        c' v (Const x) | complement x < x = Op1 Not $ c' v $ Const $ complement x
                       | x .&. 1 == 1 = Op2 Or One $ Op1 Shl1 $ c' v $ Const $ x `shiftR` 1
                       | otherwise = Op1 Shl1 $ c' v $ Const $ x `shiftR` 1

reduce :: Program -> Program
reduce (P s e) = let e' = reduce2 e
                 in if e' == e
                    then P s e' 
                    else reduce $ P s e'
  where reduce2 e = case isConst e of
          Just x -> Const x
          Nothing -> reduce1 e
        reduce1 :: Expression -> Expression
        reduce1 (Fold e0 e1 x y e2) = Fold (reduce2 e0) (reduce2 e1) x y (reduce2 e2)
        reduce1 (If0 c (Op1 Not t) (Op1 Not f)) = Op1 Not $ If0 (reduce2 c) 
                                                  (reduce2 t) (reduce2 f)
        reduce1 (If0 c t f) | t == f = reduce2 t
        reduce1 (If0 c t f) | otherwise = If0 (reduce2 c) (reduce2 t) (reduce2 f)
        reduce1 One = Const 1
        reduce1 Zero = Const 0
        reduce1 (Op1 Shl1 e) = Shift 1 (reduce2 e)
        reduce1 (Op1 Shr1 e) = Shift (-1) (reduce2 e)
        reduce1 (Op1 Shr4 e) = Shift (-4) (reduce2 e)
        reduce1 (Op1 Shr16 e) = Shift (-16) (reduce2 e)
        reduce1 (Op1 Not (Op1 Not e)) = reduce2 e
        reduce1 (Op1 Not e) = Op1 Not (reduce2 e)
        reduce1 (Op2 op e1 e2) | e1 > e2 = reduce2 (Op2 op e2 e1)
        reduce1 (Op2 And (Op1 Not e1) (Op1 Not e2)) = Op1 Not (Op2 Or (reduce2 e1) 
                                                               (reduce2 e2))
        reduce1 (Op2 Or (Op1 Not e1) (Op1 Not e2)) = Op1 Not (Op2 And (reduce2 e1) 
                                                              (reduce2 e2))
        reduce1 (Op2 And (Op2 And e1 e2) e3) | e2 == e3 = Op2 And e1 e2
        reduce1 (Op2 And e1 (Op2 And e2 e3)) | e1 == e2 = Op2 And e2 e3
        reduce1 (Op2 And e1 e2) | e1 == e2 = e1
        reduce1 (Op2 Or (Op2 Or e1 e2) e3) | e2 == e3 = Op2 Or e1 e2
        reduce1 (Op2 Or e1 (Op2 Or e2 e3)) | e1 == e2 = Op2 Or e2 e3
        reduce1 (Op2 Or e1 e2) | e1 == e2 = e1
        reduce1 (Op2 Or e (Const 0)) = e
        reduce1 (Op2 Xor e (Const 0)) = e
        reduce1 (Op2 Xor e0 e1) | e0 == e1 = Const 0
        reduce1 (Op2 And e (Const (complement -> 0))) = e
        reduce1 (Op2 Plus e (Const 0)) = e
        reduce1 (Op2 op e0 e1) = Op2 op (reduce2 e0) (reduce2 e1)
        reduce1 (Shift n (Shift m e)) | m * n > 0 = Shift (m + n) e
        reduce1 (Shift n e) = Shift n (reduce2 e)
        reduce1 x = x
