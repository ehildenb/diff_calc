module Test where

import Data.List (intercalate)
import Text.ParserCombinators.Parsec hiding (Parser)
import Text.Parsec.Prim
import Data.Functor.Identity (Identity)

type Parser = ParsecT String () Identity

data Const  = N Integer
            | Pi
            deriving Eq

data Func   = C Const
            | V Char
            | Pow Func Func
            | Exp Func
            | Ln Func
            | Cos Func
            | Sin Func
            | Neg Func
            | Mult Func Func
            | Add Func Func
            deriving Eq

-- want prettier showing, strip out extra parens
stripParens :: String -> String
stripParens ""                               = ""
stripParens str
    | (head str == '(') && (last str == ')') = stripParens . init . tail $ str
    | otherwise                              = str

instance Show Const where
    show (N i)      = show i
    show (Pi)       = "pi"

instance Show Func where
    show (V s)      = show s
    show (C c)      = show c
    show (Pow f n)  = "(" ++ stripParens (show f) ++ ")^" ++ show n
    show (Exp f)    = "e^(" ++ stripParens (show f) ++ ")"
    show (Ln f)     = "ln(" ++ stripParens (show f) ++ ")"
    show (Cos f)    = "cos(" ++ stripParens (show f) ++ ")"
    show (Sin f)    = "sin(" ++ stripParens (show f) ++ ")"
    show (Neg f)    = "-(" ++ stripParens (show f) ++ ")"
    show (Mult f g) = "(" ++ show f ++ " * " ++ show g ++ ")"
    show (Add f g)  = "(" ++ show f ++ " + " ++ show g ++ ")"

dd :: Char -> Func -> Func
dd x (C (N i))          = C (N 0)
dd x (V y)
    | x == y            = C (N 1)
    | otherwise         = C (N 0)
dd x (C Pi)             = C (N 0)
dd x (Pow f (C (N 0)))  = C (N 0)
dd x (Pow f (C (N n)))  = Mult (C (N n)) (Mult (Pow f (C (N (n - 1)))) (dd x f))
dd x (Cos f)            = Mult (Neg (Sin f)) (dd x f)
dd x (Sin f)            = Mult (Cos f) (dd x f)
dd x (Add f g)          = Add (dd x f) (dd x g)
dd x (Mult f g)         = Add (Mult (dd x f) g) (Mult f (dd x g))

-- whitespace and parens handlers
-- whitespace :: Parser String
-- whitespace = many $ oneOf "\n\t "
-- 
-- stringWS :: String -> Parser String
-- stringWS s = do whitespace
--                 str <- string s
--                 whitespace
--                 return str
-- 
-- parens :: Parser a -> Parser a
-- parens p = do stringWS "("
--               pp <- p
--               stringWS ")"
--               return pp
-- 
-- -- constant parsers
-- adigit :: Parser Char
-- adigit = oneOf ['0'..'9']
-- 
-- anInt :: Parser Integer
-- anInt = do strNum <- many1 adigit
--            return $ read strNum
-- 
-- pint :: Parser Const
-- pint = do num <- anInt
--           return $ N num
-- 
-- ppi :: Parser Const
-- ppi = do stringWS "pi"
--          return Pi
-- 
-- pvar :: Parser Const
-- pvar = do vName <- oneOf "xyz"
--           return $ V vName
-- 
-- pconst :: Parser Const
-- pconst = parens pconst <|> ppi <|> pint <|> pvar
-- 
-- -- function parsers
-- --data Func   = C Const
-- --            | Pow Func Const
-- --            | Exp Func
-- --            | Ln Func
-- --            | Cos Func
-- --            | Sin Func
-- --            | Neg Func
-- --            | Mult Func Func
-- --            | Add Func Func
-- pconstf :: Parser Func
-- pconstf = do whitespace
--              c <- pconst
--              whitespace
--              return $ C c
-- 
-- prefixFunc :: String -> (Func -> Func) -> Parser Func
-- prefixFunc str ctor = do stringWS str
--                          f <- parens pfunc
--                          return $ ctor f
-- 
-- pexp :: Parser Func
-- pexp = prefixFunc "e^" Exp
-- 
-- pln :: Parser Func
-- pln = prefixFunc "ln" Ln
-- 
-- pcos :: Parser Func
-- pcos = prefixFunc "cos" Cos
-- 
-- psin :: Parser Func
-- psin = prefixFunc "sin" Sin
-- 
-- pneg :: Parser Func
-- pneg = prefixFunc "-" Neg
-- 
-- pprefixf :: Parser Func
-- pprefixf = do f <- parens pprefixf <|> pconstf <|> pexp <|> pln <|> pcos <|> psin <|> pneg
--               whitespace
--               return f
-- 
-- infixFunc :: String -> (Func -> Func -> Func) -> Parser Func
-- infixFunc str ctor = do f <- pfunc
--                         stringWS str
--                         g <- pfunc
--                         return $ ctor f g
-- 
-- ppow :: Parser Func
-- ppow = infixFunc "^" Pow
-- 
-- ppow :: Parser Func
-- ppow = do f <- pprefix
--           stringWS "^"
--           n <- parens anInt <|> anInt
--           return $ Pow f n
-- 
-- pSubMult = ppow <|> pprefix
-- 
-- pmult :: Parser Func
-- pmult = infixFunc "*" pSubMult Mult <|> pfunc
-- 
-- padd :: Parser Func
-- padd = infixFunc "+" pmult Add <|> pfunc
-- 
-- pinfix :: Parser Func
-- pinfix = do f <- padd <|> pmult <|> ppow
--             whitespace
--             return f
-- 
-- pfunc :: Parser Func
-- pfunc = do f <- parens pfunc <|> padd
--            whitespace
--            return f
-- 
-- fromStr :: String -> Maybe Func
-- fromStr input = case parse pfunc "" input of
--                     Left _  -> Nothing
--                     Right f -> Just f
-- 
-- main :: IO ()
-- main = let testSet = [ fromStr "x^3"
--                      , fromStr "(x+3)^4"
--                      , fromStr "4 * (x+)^4"
--                      , fromStr "e^(ln(x))"
--                      ]
--        in  do mapM_ (putStrLn . show) testSet


--data Func   = C Const
--            | Pow Func Func
--            | Exp Func
--            | Ln Func
--            | Cos Func
--            | Sin Func
--            | Neg Func
--            | Mult Func Func
--            | Add Func Func

-- dd (Const a) s = Const 0
-- dd (Mono f 1) s = dd f s
-- dd (Mono f n) s = Times (Times (Const n) (Mono f (n-1))) (dd f s)
-- dd (Neg f) s = Neg (dd f s)
-- dd (Var s1) s2
--     | s1 == s2 = Const 1
--     | otherwise = Const 0
-- dd (Times f1 f2) s = Plus (Times (dd f1 s) f2) (Times f1 (dd f2 s))
-- dd (Plus f1 f2) s = Plus (dd f1 s) (dd f2 s)
-- dd (Cos f) s = Times (Neg (Sin f)) (dd f s)
-- dd (Sin f) s = Times (Cos f) (dd f s)
--
--innerProduct :: Floating a => Bra a -> Ket a -> a
--innerProduct (B b) (K k)
--    | b == k    = 1
--    | otherwise = 0
--innerProduct (Sb s b) k = s * (innerProduct b k)
--innerProduct b (Sk s k) = s * (innerProduct b k)
--innerProduct (Lb bs) k  = sum (map (flip innerProduct k) bs)
--innerProduct b (Lk ks)  = sum (map (innerProduct b) ks)
--
--toStr :: Show a => Fit a -> String
--toStr (Gauss mu sigma) = "e^(-(x-" ++ show mu ++ ")^2) / (" ++ show sigma ++ "^2)"
--toStr (Sum []) = "0"
--toStr (Sum (g:gs)) = toStr g ++ " + " ++ toStr (Sum gs)
--toStr (Scale s g) = show s ++ " * (" ++ toStr g ++ ")"
--
--eval :: Floating a => Fit a -> a -> a
--eval (Gauss mu sigma) x = exp (-(x - mu)^2) / (sigma^2)
--eval (Sum fs) x = sum (map (flip eval x) fs)
--eval (Scale s f) x = s * (eval f x)
