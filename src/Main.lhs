> module Main where

> import qualified Data.Map as Map
> import Data.List (elemIndex)
> import Data.Either (partitionEithers)
> import Data.Foldable (foldl')
> import Data.Char (isAlpha, isDigit)
> import Data.Functor (($>))
> import GHC.IO.Handle (hFlush, hClose)
> import System.IO (stdout, IOMode(WriteMode), openFile)
> import qualified Data.ByteString as B
> import Data.Word (Word8)
> import Data.Maybe (fromMaybe)
> import qualified Data.Set as Set
> import System.Process (system)
> import Control.Monad (when)

> main :: IO ()
> main = do
>   putStr "> "
>   hFlush stdout
>   src <- getLine
>   when (src /= "q") $ do
>     let pos = Pos "input" 1 1
>     case run parseTerm Nothing pos src of
>       Left err -> putStrLn err
>       Right (t, _, "") -> do
>         let res = translate 0 Map.empty t
>         case res of
>           Left err -> putStrLn err
>           Right t2 -> do
>             let bytecode = codegen [] t2 ++ [29, 0]
>             h_out <- openFile "bin.fvm" WriteMode
>             B.hPut h_out $ B.pack bytecode
>             hClose h_out
>             _ <- system "vendor/fvm bin.fvm"
>             return ()
>       Right (_, p, c:_) ->
>         putStrLn $
>           prettyParseError p Nothing $ "unexpected `" ++ c:"`"
>     main

> data Pos = Pos String Int Int deriving Show

> class Pretty a where
>   pretty :: a -> String

> data Syntax = LambdaSyntax Pos String Syntax
>             | IdentSyntax Pos String
>             | AppSyntax Pos Syntax Syntax
>             | NatSyntax Pos Int
>             deriving Show

> stxPos :: Syntax -> Pos
> stxPos stx = case stx of
>   LambdaSyntax p _ _ -> p
>   IdentSyntax p _ -> p
>   AppSyntax p _ _ -> p
>   NatSyntax p _ -> p

> instance Pretty Syntax where
>   pretty stx = case stx of
>     LambdaSyntax _ x e -> x ++ "-> " ++ pretty e
>     IdentSyntax _ s -> s
>     AppSyntax _ f a -> "(" ++ pretty f ++ ")(" ++ pretty a ++ ")"
>     NatSyntax _ n -> show n

> data Term = Lambda Pos String Term
>           | Ident Pos Int String
>           | App Pos Term Term
>           | Nat Pos Int
>           deriving Show

> instance Pretty Term where
>   pretty t = case t of
>     Lambda _ x e -> x ++ "-> " ++ pretty e
>     Ident _ _ x -> x
>     App _ foo bar -> "(" ++ pretty foo ++ ")(" ++ pretty bar ++ ")"
>     Nat _ n -> show n

> newtype Parser a = Parser {
>   run :: Maybe String -> Pos -> String -> Either String (a, Pos, String)
> }

> prettyParseError :: Pos -> Maybe String -> String -> String
> prettyParseError (Pos srcName line col) expected msg =
>   "Parse error. "
>   ++ msg ++ " in `" ++ srcName ++ "` at "
>   ++ show line ++ ":" ++ show col ++ "."
>   ++ case expected of
>     Just s -> " Expected " ++ s ++ "."
>     Nothing -> ""

> position :: Parser Pos
> position = Parser $ \_ pos src -> Right (pos, pos, src)

> satisfy :: (Char -> Bool) -> Parser Char
> satisfy p = Parser $ \expected (Pos srcName line col) src ->
>   case src of
>     c:rest | c == '\n' && p c -> Right (c, Pos srcName (line + 1) 0, rest)
>     c:rest | p c -> Right (c, Pos srcName line (col + 1), rest)
>     c:_ -> Left $
>       prettyParseError (Pos srcName line col) expected $ "Unexpected `" ++ c:"`"
>     [] -> Left $
>       prettyParseError (Pos srcName line col) expected "Unexpected end of input"

> instance Functor Parser where
>   fmap f p = Parser $ \expected pos s -> case run p expected pos s of
>     Left err -> Left err
>     Right (x, pos2, rest) -> Right (f x, pos2, rest)

> instance Applicative Parser where
>   pure x = Parser $ \_ pos s -> Right (x, pos, s)
>   pf <*> pa = Parser $ \expected pos s -> do -- Either monad, not Parser monad
>     (f, pos2, rest) <- run pf expected pos s
>     (a, pos3, rest2) <- run pa expected pos2 rest
>     Right (f a, pos3, rest2)

> instance Monad Parser where
>   return = pure
>   pa >>= f = Parser $ \expected pos s -> do
>     (a, pos2, rest) <- run pa expected pos s
>     run (f a) expected pos2 rest

> char :: Char -> Parser Char
> char c = satisfy (==c)

> oneOf :: [Parser a] -> Parser a
> oneOf [p] = p
> oneOf (p:ps) = Parser $ \expected pos s -> case run p expected pos s of
>   Left _err -> run (oneOf ps) expected pos s
>   Right (x, pos2, rest) -> Right (x, pos2, rest)
> oneOf [] = error "oneOf on empty list of parsers"

> possible :: Parser a -> Parser (Maybe a)
> possible p = oneOf [fmap Just p, return Nothing]

> many0 :: Parser a -> Parser [a]
> many0 p = Parser $ \expected pos s -> case run p expected pos s of
>   Left _ -> Right ([], pos, s)
>   Right (x, pos2, rest) -> run ((x:) <$> many0 p) expected pos2 rest

> many :: Parser a -> Parser [a]
> many p = Parser $ \expected pos s -> do -- Either monad, not Parser monad
>   (x, pos2, rest) <- run p expected pos s
>   run ((x:) <$> many0 p) expected pos2 rest

> exact :: String -> Parser String
> exact s = foldr (\c p-> char c *> p) (return ()) s $> s

> sepBy :: Parser a -> Parser b -> Parser [b]
> sepBy by p = do
>   b <- p
>   bs <- many0 (by >> p)
>   return (b:bs)

> sepBy0 :: Parser a -> Parser b -> Parser [b]
> sepBy0 by p = oneOf [sepBy by p, return []]

> comment :: Parser Char
> comment = do
>   _ <- exact "//"
>   _ <- many0 $ satisfy (/='\n')
>   _ <- possible $ char '\n'
>   return '\n'

> whitespace0 :: Parser [Char]
> whitespace0 = many0 $ oneOf [char ' ', char '\n', comment]

> whitespace :: Parser [Char]
> whitespace = many $ oneOf [char ' ', char '\n', comment]

> identString :: Parser String
> identString = do
>   first <- satisfy isAlpha
>   rest <- many0 $ oneOf [satisfy isAlpha, char '_', satisfy isDigit]
>   return (first:rest)

> patternString :: Parser String
> patternString = oneOf
>   [ identString
>   , do
>     _ <- char '_'
>     mb_rest <- possible identString
>     case mb_rest of
>       Just rest -> return $ '_':rest
>       Nothing -> return "_"
>   ]

> parseIdentOrLambda :: Parser Syntax
> parseIdentOrLambda = do
>   p <- position
>   i <- identString
>   _ <- whitespace0
>   mb_arrow <- possible (exact "->")
>   case mb_arrow of
>     Just _ -> LambdaSyntax p i <$> parseTerm
>     Nothing -> return $ IdentSyntax p i

> parseConstantLambda :: Parser Syntax
> parseConstantLambda = do
>   p <- position
>   s <- patternString
>   _ <- whitespace0
>   _ <- exact "->"
>   LambdaSyntax p s <$> parseTerm

> data LetType = Basic | Back

> parseLet :: Parser Syntax
> parseLet = do
>   p <- position
>   _ <- exact "let"
>   _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
>   i <- patternString
>   _ <- whitespace0
>   (ident, let_type, params) <- do
>     mb_params <- possible parseParams
>     case mb_params of
>       Just params -> do
>         _ <- whitespace0
>         _ <- char '='
>         return (i, Basic, params)
>       Nothing -> do
>         op <- oneOf [exact "=", exact "<-"]
>         case op of
>           "=" -> return (i, Basic, [])
>           "<-" -> return (i, Back, [])
>           _ -> error "internal error"
>   val <- parseTerm
>   _ <- exact "in"
>   _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
>   scope <- parseTerm
>   let val2 = foldr (LambdaSyntax p) val params
>   return $ case let_type of
>     Basic -> AppSyntax p (LambdaSyntax p ident scope) val2
>     Back -> AppSyntax p val (LambdaSyntax p ident scope)

> parseParens :: Parser Syntax
> parseParens = char '(' *> parseTerm <* char ')'

> parseNat :: Parser Syntax
> parseNat = NatSyntax <$> position <*> (read <$> many (satisfy isDigit))

> parseTermNoPostfix :: Parser Syntax
> parseTermNoPostfix = do
>   _ <- whitespace0
>   t <- oneOf
>     [ parseParens
>     , parseNat
>     , parseConstantLambda
>     , parseLet
>     , parseIdentOrLambda
>     ]
>   _ <- whitespace0
>   return t

> data Postfix = AppPostfix Pos Syntax
> --             | MonoidPostfix Pos [Syntax]
>              | ApostrophePrefix Pos Syntax

> parseTerm :: Parser Syntax
> parseTerm = do
>   t <- parseTermNoPostfix
>   args <- many0 $ oneOf
>     [ AppPostfix <$> position <*> parseParens
>     {- , do
>       p2 <- position
>       _ <- char '['
>       terms <- sepBy0 (char ',') parseTerm
>       _ <- char ']'
>       _ <- whitespace0
>       return $ MonoidPostfix p2 terms -}
>     , do
>       p2 <- position
>       _ <- char '\''
>       ApostrophePrefix p2 <$> parseTerm
>     ]
>   let out = case args of
>         [] -> t
>         _ -> foldl' (\b a-> case a of
>             AppPostfix p2 arg -> AppSyntax p2 b arg
>             {- MonoidPostfix p2 terms ->
>               foldr (\term so_far->
>                   AppSyntax p2
>                       (AppSyntax p2
>                           (AccessSyntax (stxPos b) b "Has")
>                         term)
>                     so_far
>                 ) (AccessSyntax (stxPos b) b "Empty") terms -}
>             ApostrophePrefix p2 rhs -> AppSyntax p2 b rhs
>           ) t args
>   _ <- whitespace0
>   return out

> parseParams :: Parser [String]
> parseParams = many $ do
>           _ <- char '('
>           _ <- whitespace0
>           param <- patternString
>           _ <- whitespace0
>           _ <- char ')'
>           return param

> parseDecl :: Parser (Either (String, Syntax) [String])
> parseDecl = do
>   p <- position
>   _ <- exact "def"
>   _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
>   name <- identString
>   mb_not_func <- possible (whitespace0 >> char ':')
>   case mb_not_func of
>     Just _ -> do
>       _ <- whitespace0
>       t <- parseTerm
>       return $ Left (name, t)
>     Nothing -> do
>       params <- parseParams
>       _ <- whitespace0
>       _ <- char ':'
>       body <- parseTerm
>       let body2 = foldr (LambdaSyntax p) body params
>       return $ Left (name, body2)

> parseFile :: Parser (Map.Map String Syntax, [[String]])
> parseFile = do
>   let parser = many $ whitespace0 *>
>         parseDecl <* whitespace0
>   (decls, imports) <- fmap partitionEithers parser
>   return (Map.fromList decls, imports)

> translate :: Int -> Map.Map String Int -> Syntax -> Either String Term
> translate index renames t =
>   let tr = translate in
>   case t of
>     LambdaSyntax p param body -> do
>       body2 <- tr (index + 1) (Map.insert param index renames) body
>       return $ Lambda p param body2
>     IdentSyntax p ('#':name) -> return $ Ident p 0 $ '#':name
>     IdentSyntax p name ->
>       case Map.lookup name renames of
>         Just i -> return $ Ident p (index - i - 1) name
>         Nothing -> Left $ prettyParseError p Nothing $ "undefined variable `" ++ name ++ "`"
>     AppSyntax p foo bar -> do
>       foo2 <- tr index renames foo
>       bar2 <- tr index renames bar
>       return $ App p foo2 bar2
>     NatSyntax p n -> return $ Nat p n

> fvs :: [Int] -> Int -> Term -> Set.Set Int
> fvs caps depth t = case t of
>   Lambda _ _ body -> Set.map (\n->n-1) $ fvs caps (depth + 1) body
>   Ident _ i _ ->
>     if i < depth then Set.empty else Set.singleton i
>   App _ foo bar -> fvs caps depth foo `Set.union` fvs caps depth bar
>   Nat _ _ -> Set.empty

> lamOp :: Int -> [Word8]
> lamOp n = [0, fromIntegral n]
> appOp :: [Word8]
> appOp = [1]
> varOp :: Int -> [Word8]
> varOp n = [2, fromIntegral n]
> retOp :: [Word8]
> retOp = [3]
> litOp :: Int -> [Word8]
> litOp n = [4, fromIntegral n]
> capOp :: Int -> [Word8]
> capOp n = [5, fromIntegral n]

> codegen :: [Int] -> Term -> [Word8]
> codegen caps t = case t of
>   Lambda _ _ body -> 
>     let body_caps = Set.toAscList $ fvs [] 1 body in
>     let body_cap_indices = map (\n->fromMaybe (-1) (elemIndex (n-1) caps) + 1) body_caps in
>     let body_ops = codegen body_caps body in
>     concatMap capOp (reverse body_cap_indices) ++ lamOp (length body_ops + 1) ++ body_ops ++ retOp
>   Ident _ i _ -> 
>     case elemIndex i caps of
>       Just idx -> varOp (idx + 1)
>       Nothing -> varOp 0
>   App _ foo bar -> codegen caps foo ++ codegen caps bar ++ appOp
>   Nat _ n -> litOp n