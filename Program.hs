{-# LANGUAGE TupleSections #-}

module Program where

import Data.Bits ( (.&.), (.|.), complement, shiftL, shiftR, xor )
import Data.Int ( Int64 )
import Data.List ( nub, sort )
import Text.ParserCombinators.Parsec ( Parser,
                                       choice, letter, many1,
                                       parse, spaces, string, try, 
                                       getPosition, sourceColumn )

data Program = P { param :: String, unP ::  Expression }
             deriving ( Eq, Ord )
data Expression = Zero | One | Id String
                | If0 Expression Expression Expression
                | Fold Expression Expression String String Expression
                | Op1 Op1 Expression
                | Op2 Op2 Expression Expression
                deriving ( Eq, Ord )
data Op1 = Not | Shl1 | Shr1 | Shr4 | Shr16
         deriving ( Bounded, Eq, Enum, Ord )
data Op2 = And | Or | Xor | Plus
         deriving ( Bounded, Eq, Enum, Ord )

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

instance Show Op1 where
  show op = snd $ head $ filter ((==op) . fst) [(Not, "not"), (Shl1, "shl1"),
                                                (Shr1, "shr1"), (Shr4, "shr4"),
                                                (Shr16, "shr16")]

instance Show Op2 where
  show op = snd $ head $ filter ((==op) . fst) [(And, "and"), (Or, "or"),
                                                (Xor, "xor"), (Plus, "plus")]

instance Read Program where
  readsPrec _ s = case parse (do p <- parseProgram    -- arrows?
                                 pos <- getPosition
                                 return (pos, p)) "" s of
                    Right (pos, p) -> [(p, drop (sourceColumn pos - 1) s)]
                    Left err -> error $ show err

bytes :: Int64 -> [Int64]
bytes = take 8 . drop 1 . map fst . iterate next . (0,)
  where next (a, b) = (b .&. 0xff, b `shiftR` 8)

evaluate :: Program -> Int64 -> Int64
evaluate (P s e) x = evaluate' [(s, x)] e
  where evaluate' _ Zero = 0
        evaluate' _ One = 1
        evaluate' v (Id s') = snd $ head $ filter ((== s') . fst) v
        evaluate' v (If0 c t f) = if evaluate' v c == 0 
                                  then evaluate' v t 
                                  else evaluate' v f
        evaluate' v (Fold arg start sy sz accum) = foldr f (evaluate' v start) $ 
                                                   bytes $ evaluate' v arg
          where f y z = evaluate' ((sy, y):(sz, z):v) accum
        evaluate' v (Op1 op e) = op1 op $ evaluate' v e
        evaluate' v (Op2 op y z) = op2 op (evaluate' v y) (evaluate' v z)

op1 :: Op1 -> Int64 -> Int64
op1 Not = complement
op1 Shl1 = flip shiftL 1
op1 Shr1 = flip shiftR 1
op1 Shr4 = flip shiftR 4
op1 Shr16 = flip shiftR 16

op2 :: Op2 -> Int64 -> Int64 -> Int64
op2 And = (.&.)
op2 Or = (.|.)
op2 Xor = xor
op2 Plus = (+)

size :: Program -> Int
size (P _ e) = 1 + size' e
  where size' Zero = 1
        size' One = 1
        size' (Id _) = 1
        size' (If0 c t f) = 1 + size' c + size' t + size' f
        size' (Fold e0 e1 _ _ e2) = 2 + size' e0 + size' e1 + size' e2
        size' (Op1 _ e) = 1 + size' e
        size' (Op2 _ e0 e1) = 1 + size' e0 + size' e1

op :: Expression -> [String]
op = nub . sort . op'
  where op' Zero = []
        op' One = []
        op' (Id _) = []
        op' (If0 c t f) = "if0" : op' c ++ op' t ++ op' f
        op' (Fold e0 e1 _ _ e2) = "fold" : op' e0 ++ op' e1 ++ op' e2
        op' (Op1 op e) = show op : op' e
        op' (Op2 op e0 e1) = show op : op' e0 ++ op' e1

-- | Note: in the spec this is described as a binary relation, but
-- it seems like the second argument is strictly dependent on the
-- first, so I'm implementing it as a function.
operators :: Program -> [String]
operators (P _ (Fold e0 e1 _ _ e2)) = nub $ sort $ "tfold" : op e0 ++ op e1 ++ op e2
operators (P _ e) = op e

parseProgram :: Parser Program
parseProgram = do string "(" >> spaces
                  string "lambda" >> spaces
                  string "(" >> spaces
                  s <- many1 letter
                  spaces >> string ")" >> spaces
                  e <- parseExpr
                  spaces >> string ")"
                  return $ P s e

parseExpr :: Parser Expression
parseExpr = choice $ map try $ [string "0" >> return Zero,
                                string "1" >> return One,
                                Id `fmap` many1 letter,
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
                                   id0 <- spaces >> many1 letter
                                   id1 <- spaces >> many1 letter
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
                                   return $ Op2 op e0 e1]

parseEnum :: (Bounded a, Enum a, Show a) => Parser a
parseEnum = try $ do w <- many1 letter
                     (a:[]) <- return $ filter ((==w) . show) [minBound..maxBound]
                     return a
