{-# LANGUAGE TupleSections #-}

module Program where

import Data.Bits ( (.&.), (.|.), complement, shift, shiftL, shiftR, xor )
import Data.Char ( ord, toLower )
import Data.List ( nub, sort )
import Data.Maybe ( fromJust )
import Data.Word ( Word64 )
import Text.ParserCombinators.Parsec ( Parser, (<|>), oneOf,
                                       char, choice, digit, letter,
                                       many, many1, parse, spaces,
                                       string, try, getPosition,
                                       sourceColumn )

data Program = P { param :: String, unP ::  Expression }
             deriving ( Eq, Ord )
data Expression = Zero | One | Id String
                | If0 Expression Expression Expression
                | Fold Expression Expression String String Expression
                | Op1 Op1 Expression
                | Op2 Op2 Expression Expression
                | Shift Int Expression
                deriving ( Eq, Ord )
data Op1 = Not | Shl1 | Shr1 | Shr4 | Shr16
         deriving ( Bounded, Eq, Enum, Ord )
data Op2 = And | Or | Xor | Plus
         deriving ( Bounded, Eq, Enum, Ord )

data Op = Cond | CFold | TFold | Unary Op1 | Binary Op2
        deriving ( Eq, Ord )

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

evaluate :: Program -> Word64 -> Word64
evaluate (P s e) x = evaluate' [(s, x)] e
  where evaluate' _ Zero = 0
        evaluate' _ One = 1
        evaluate' v (Id s') = fromJust $ lookup s' v
        evaluate' v (If0 c t f) = if evaluate' v c == 0 
                                  then evaluate' v t 
                                  else evaluate' v f
        evaluate' v (Fold arg start sy sz accum) = foldr f (evaluate' v start) $ 
                                                   reverse $ bytes $ evaluate' v arg
          where f y z = evaluate' ((sy, y):(sz, z):v) accum
        evaluate' v (Op1 op e) = op1 op $ evaluate' v e
        evaluate' v (Op2 op y z) = op2 op (evaluate' v y) (evaluate' v z)
        evaluate' v (Shift n e) = shift (evaluate' v e) n

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
