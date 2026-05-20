module SMT where
import System.Process
import Data.List
import Data.Either
import System.IO
import Data.Char

data Exp =
    Var String
  | Val Int
  | Plus [Exp]
  | Times [Exp]
  | Ite Formula Exp Exp
  deriving Eq

data Formula =
    And [Formula]
  | Or [Formula]
  | Not Formula
  | Distinct [Exp]
  | Geq Exp Exp
  | Gt Exp Exp
  | Eq Exp Exp
  | Iff Formula Formula
  | FVar String
  deriving Eq

data Command =
    DeclareInt String
  | DeclareBool String
  | Assert Formula
  | AssertSoft Formula
  | CheckSat
  | GetValue [String]
  | Reset

type SMTInput = [Command]

-- Escape/unescape functions for identifiers in SMT solvers.

escape' :: String -> String
escape' []         = []
escape' ('_' : cs) = "__" ++ escape' cs
escape' (c : cs)
  | isAlphaNum c = c : escape' cs
  | otherwise    = "_x" ++ show (fromEnum c) ++ "_" ++ escape' cs

escape :: String -> String
escape s = '_': escape' s

unescape' :: String -> String
unescape' [] = []
unescape' ('_' : 'x' : cs)
  | (s, _ : cs') <- break (== '_') cs = chr (read s :: Int) : unescape' cs'
unescape' "_"             = error "unexpacted end of string"
unescape' ('_': '_' : cs) = '_' : unescape' cs
unescape' ('_': c : _)    = error ("unknown escape code: " ++ [c])
unescape' (c : cs)        = c : unescape' cs

unescape :: String -> String
unescape ('_' : cs) = unescape' cs
unescape s          = error ("unexpected string: " ++ show s)

-- Pretty printers.

showApplication :: Show a => String -> [a] -> String
showApplication s xs =
  "(" ++ intercalate " " (s : [ show x | x <- xs ]) ++ ")"

instance Show Exp where
  show (Val n)       = show n
  show (Var x)       = escape x
  show (Plus [])     = "0"
  show (Plus [e])    = show e
  show (Plus es)     = showApplication "+" es
  show (Times [])    = "1"
  show (Times [e])   = show e
  show (Times es)    = showApplication "*" es
  show (Ite f e1 e2) = "(ite " ++ show f ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"

instance Show Formula where
  show (And [])       = "true"
  show (Or [])        = "false"
  show (And [f])      = show f
  show (Or [f])       = show f
  show (And fs)       = showApplication "and" fs
  show (Or fs)        = showApplication "or"  fs
  show (Not f)        = showApplication "not" [f]
  show (Distinct [])  = "true"
  show (Distinct es)  = showApplication "distinct" es
  show (Gt e1 e2)     = showApplication ">"   [e1,e2]
  show (Geq e1 e2)    = showApplication ">="  [e1,e2]
  show (Eq e1 e2)     = showApplication "="   [e1,e2]
  show (Iff f1 f2)    = showApplication "="   [f1,f2]
  show (FVar x)       = escape x

instance Show Command where
  show (DeclareInt x)  = "(declare-fun " ++ escape x ++ " () Int)"
  show (DeclareBool x) = "(declare-fun " ++ escape x ++ " () Bool)"
  show (Assert f)      = showApplication "assert" [f]
  show (AssertSoft f)  = showApplication "assert-soft" [f]
  show CheckSat        = "(check-sat)"
  show (GetValue [])   = ""
  show (GetValue xs)   = "(get-value (" ++ intercalate " " [ escape x | x <- xs ] ++ "))"
  show Reset           = "(reset)"

showSMTInput :: [Command] -> String
showSMTInput cs = unlines [ show c | c <- cs ]

-- Constructors.

top :: Formula
top = And []

bottom :: Formula
bottom = Or []

neg :: Formula -> Formula
neg (Or [])  = And []
neg (And []) = Or []
neg (Not f)  = f
neg f        = Not f

conj :: [Formula] -> Formula
conj fs
  | elem (Or []) fs' = Or []
  | [f] <- fs'       = f
  | otherwise        = And fs'
  where fs' = [ f | f <- fs, f /= And [] ]

disj :: [Formula] -> Formula
disj fs
  | elem (And []) fs' = And []
  | [f] <- fs'        = f
  | otherwise         = Or fs'
  where fs' = [ f | f <- fs, f /= Or [] ]

implies :: Formula -> Formula -> Formula
implies f1 f2 = disj [neg f1, f2]

iff :: Formula -> Formula -> Formula
iff f (And []) = f
iff (And []) f = f
iff f (Or [])  = Not f
iff (Or []) f  = Not f
iff f1      f2 = Iff f1 f2

plus :: [Exp] -> Exp
plus es =
  case es' of
    [] -> Val 0
    [e] -> e
    _   -> Plus es'
  where es' = [ e | e <- es, e /= Val 0 ]

boolToFormula :: Bool -> Formula
boolToFormula True  = And []
boolToFormula False = Or []

eq :: Exp -> Exp -> Formula
eq (Val m) (Val n) = boolToFormula (m == n)
eq e1      e2      = Eq e1 e2

geq :: Exp -> Exp -> Formula
geq (Val m) (Val n) = boolToFormula (m >= n)
geq e1      e2      = Geq e1 e2

gt :: Exp -> Exp -> Formula
gt (Val m) (Val n) = boolToFormula (m > n)
gt e1      e2      = Gt e1 e2

ite :: Formula -> Exp -> Exp -> Exp
ite (And []) e _ = e
ite (Or  []) _ e = e
ite f1 (Ite f2 e (Val m)) (Val n)
  | m == n = ite (conj [f1,f2]) e (Val n)
ite f e1 e2 = Ite f e1 e2

times01 :: Formula -> Exp -> Exp
times01 f e = ite f e (Val 0)

-- Evaluation functions.

distinct :: Eq a => [a] -> Bool
distinct []       = True
distinct (x : xs) = all (/= x) xs && distinct xs

-- Functions for expressions and formulas.

variables_exp :: Exp -> [Either String String]
variables_exp (Var x)       = [Left x]
variables_exp (Val _)       = []
variables_exp (Plus es)     = variables_exps es
variables_exp (Times es)    = variables_exps es
variables_exp (Ite f e1 e2) =
  nub (variables_formula f ++ variables_exp e1 ++ variables_exp e2)

variables_exps :: [Exp] -> [Either String String]
variables_exps es = nub [ x | e <- es, x <- variables_exp e ]

variables_formula :: Formula -> [Either String String]
variables_formula (FVar x)      = [Right x]
variables_formula (Distinct es) = variables_exps es
variables_formula (Geq e1 e2)   = variables_exps [e1, e2]
variables_formula (Eq e1 e2)    = variables_exps [e1, e2]
variables_formula (Gt e1 e2)    = variables_exps [e1, e2]
variables_formula (Not f)       = variables_formula f
variables_formula (And fs)      = variables_formulas fs
variables_formula (Or fs)       = variables_formulas fs
variables_formula (Iff f1 f2)   = variables_formulas [f1, f2]

variables_formulas :: [Formula] -> [Either String String]
variables_formulas fs = nub [ x | f <- fs, x <- variables_formula f ]

variables :: Formula -> ([String], [String])
variables f = partitionEithers (variables_formula f)

-- Running an SMT solver.

check_sat :: String -> SMTInput -> IO Bool
check_sat tool input = do
  (Just hin, Just hout, _, _) <- createProcess (proc tool ["/dev/stdin"]) {
    std_in = CreatePipe,
    std_out = CreatePipe }
  hPutStr hin (showSMTInput (input ++ [CheckSat]))
  hClose hin
  s <- hGetContents hout
  return $ s == "sat\n"
