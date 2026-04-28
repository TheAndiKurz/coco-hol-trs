{-# LANGUAGE ViewPatterns      #-}

module Parser where

import Control.Applicative
import Data.Char (isSpace)
import Data.List (lines, elemIndex, sort, group)
import TRS
import Data.ByteString.Char8 (split)

data Input = Input
    { inputLine :: Integer
    , inputChar :: Integer
    , inputStr :: String
    , inputComplete :: String
    , fileName :: String
    } deriving Show

newInput :: String -> String -> Input
newInput name input_string = Input 1 1 input_string input_string name

-- Pull the first character of the input if there is one still input
inputHead :: Input -> Maybe (Char, Input)
inputHead (Input _ _ [] _ _)       = Nothing
inputHead (Input line char (x:xs) i fs)
  | x == '\n' = Just (x, Input (line + 1) 1 xs i fs)
  | otherwise = Just (x, Input line (char + 1) xs i fs)

data ParseError = ParseError Input String

newtype Parser a = Parser
    { runParser :: Input -> Either [ParseError] (Input, a)
    }

newParseError :: ParseError -> Either [ParseError] (Input, a)
newParseError err = Left [err]

parserError :: String -> Parser a
parserError err = Parser $ \input -> Left [ParseError input err]

instance Functor Parser where
    fmap f (Parser p) =
        Parser $ \input -> do
            (input', x) <- p input
            return (input', f x)

instance Monad Parser where
    (Parser p) >>= f = Parser $ \s -> do
        (s', a) <- p s
        runParser (f a) s'

instance Applicative Parser where
    pure x = Parser $ \input -> Right (input, x)
    (Parser p1) <*> (Parser p2) =
        Parser $ \input -> do
            (input', f) <- p1 input
            (input'', a) <- p2 input'
            return (input'', f a)

instance Alternative (Either [ParseError]) where
  empty = Left []
  Left e1 <|> Left e2 = Left (e1 ++ e2)
  Left _ <|> e2 = e2
  e1 <|> _ = e1

instance Alternative Parser where
  empty = Parser $ const empty
  (Parser p1) <|> (Parser p2) =
    Parser (\input -> p1 input <|> p2 input)

instance Show ParseError where
  show (ParseError input err) = 
    let line_number = fromIntegral $ inputLine input - 1
        char_number = fromIntegral $ inputChar input - 1
        ls = lines $ inputComplete input
        line_number_str = show $ line_number + 1
        spaces n = take n (repeat ' ')
    in
    "Error in " ++ (fileName input) ++ ":" ++ line_number_str ++ ":" ++ show (char_number + 1) ++ "\n" ++ line_number_str ++ " | " ++ (ls !! line_number) ++ "\n" ++ spaces (length line_number_str) ++ " | " ++ spaces char_number ++ "^\n" ++ err ++ "\n"

-- Parser for single character
charP :: Char -> Parser Char
charP c = Parser f
    where
        f input@(inputHead -> Just (x, xs))
            | c == x = Right (xs, c)
            | otherwise = newParseError $ ParseError input
                ("Expected '" ++ [c] ++ "', but found '" ++ [x] ++ "'")
        f input = newParseError $ ParseError input
            ("Expected '" ++ [c] ++ "', but reached end of input.")

-- Parser for specific string
stringP :: String -> Parser String
stringP str =
    Parser $ \input ->
        case runParser (traverse charP str) input of
            Left _ -> Left [ParseError input
                    ("Expected \"" ++ str ++ "\", but found \"" ++ (take (length str) (inputStr input)) ++ "\"")]
            result -> result

peekString :: String -> Parser Bool
peekString str = Parser $ \input ->
    Right (input, take (length str) (inputStr input) == str)

-- Parser that discards whitespace
dropWhileP :: (Char -> Bool) -> Parser ()
dropWhileP f = Parser $ \input ->
    case inputHead input of
        Just (x, input') | f x -> runParser (dropWhileP f) input'
        _ -> Right (input, ())

ws :: Parser ()
ws = dropWhileP isSpace

void :: Parser ()
void = ws *> (Parser $ \input ->
    case inputHead input of
        Just (x, input') | x == ';' -> runParser (dropWhileP (/= '\n') *> void) input'
        _ -> Right (input, ()))


-- Parser of a character that satisfies a predicate
parseIf :: String         -- Description of the predicate
        -> (Char -> Bool) -- predicate
        -> Parser Char
parseIf desc f =
  Parser $ \input ->
    case input of
        (inputHead -> Just (y, ys))
            | f y -> Right (ys, y)
            | otherwise -> newParseError $
                ParseError
                    input
                    ("Expected " ++ desc ++ ", but found '" ++ [y] ++ "'")
        _ -> newParseError $
            ParseError
                input
                ("Expected " ++ desc ++ ", but reached end of string")

identCharP :: Parser Char
identCharP = parseIf "identifier character" ((&&) <$> (not . isSpace) <*> (not . (`elem` "()")))

parensP :: Parser a -> Parser a
parensP p = void *> charP '(' *> void *> p <* void <* charP ')'

idP :: Parser Id
idP = void *> (Id <$> some identCharP)

sortP :: Parser Sort
sortP = parensP $ void *> stringP "sort" *> void *> (Sort <$> idP)

-- data Type     = TypeSort Integer | TypeFunction [Type] deriving Show
typeP :: Parser Type
typeP = void *> (functionP <|> sortP)
    where
        functionP = do
            types <- parensP $ stringP "->" *> void *> (some typeP)
            case last types of
                (Type [] sort) -> pure $ Type (take (length types - 1) types) sort
                _ -> parserError "return type of a function is not a sort"
        sortP = void *> (Type <$> pure [] <*> idP)

functionP :: Parser Var
functionP = parensP $ stringP "fun" *> void *> (Var <$> idP <*> typeP)

parseVar :: Parser Var
parseVar = void *> (parensP $ Var <$> idP <*> typeP)

termP :: Parser Term
termP = atomP <|> applicationP <|> lambdaP
    where
        lambdaP = void *> 
            (parensP $ stringP "lambda" *> void *>
                (TermLambda <$>
                    (parensP $ (some parseVar))
                    <*> termP
                )
            )

        applicationP = void *> charP '(' *> (Term <$> idP <*> some termP)  <* charP ')'

        atomP = Term <$> idP <*> pure []

ruleP :: Parser Rule
ruleP = parensP $ stringP "rule" *> void *> (Rule <$> termP <*> termP)


holSystemP :: Parser HOLSystem
holSystemP = do
    _ <- void *> stringP "(format higher-order)"

    let parseSorts = do
          isSort <- void *> peekString "(sort"
          if isSort then (:) <$> sortP <*> parseSorts else pure []

    sorts <- parseSorts

    let parseFuns = do
          isFun <- void *> peekString "(fun"
          if isFun then (:) <$> functionP <*> parseFuns else pure []

    functions <- parseFuns

    let parseRules = do
          isRule <- void *> peekString "(rule"
          if isRule then (:) <$> ruleP <*> parseRules else pure []

    rules <- parseRules

    return $ HOLSystem sorts functions rules
