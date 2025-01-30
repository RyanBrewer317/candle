> {-# LANGUAGE GADTs #-}
> module Main where

> import qualified Data.Map as Map
> import Data.List (elemIndex, intercalate)
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
> import System.Environment (getArgs)

> main :: IO ()
> main = do
>   args <- getArgs
>   case args of
>     [] -> do
>       putStr "> "
>       hFlush stdout
>       src <- getLine
>       when (src /= "q") $ do
>         let pos = Pos "input" 1 1
>         case run parseTerm Nothing pos src of
>           Left err -> putStrLn err
>           Right (t, _, "") -> do
>             let res = translate 0 Map.empty [] t
>             case res of
>               Left err -> putStrLn err
>               Right t2 -> do
>                 case infer Nothing [] t2 of
>                   Left err -> putStrLn [head err]
>                   Right _t3 -> do
>                     let bytecode = codegen [] [] t2 ++ [29, 0]
>                     h_out <- openFile "bin.fvm" WriteMode
>                     B.hPut h_out $ B.pack bytecode
>                     hClose h_out
>                     _ <- system "vendor/fvm bin.fvm"
>                     return ()
>           Right (_, p, c:_) ->
>             putStrLn $
>               prettyParseError p Nothing $ "unexpected `" ++ c:"`"
>         main
>     filename:_ -> do
>       let pos = Pos filename 1 1
>       src <- readFile filename
>       case run parseTerm Nothing pos src of
>         Left err -> putStrLn err
>         Right (t, _, "") -> do
>           let res = translate 0 Map.empty [] t
>           case res of
>             Left err ->
>               putStrLn err
>             Right t2 -> do
>               case infer Nothing [] t2 of
>                 Left err -> putStrLn err
>                 Right _t3 -> do
>                   let bytecode = codegen [] [] t2 ++ [29, 0]
>                   h_out <- openFile "bin.fvm" WriteMode
>                   B.hPut h_out $ B.pack bytecode
>                   hClose h_out
>                   putStrLn "success!"
>                   -- _ <- system "vendor/fvm bin.fvm"
>                   putStrLn $ pretty $ normalize [] t2
>                   return ()
>         Right (_, p, c:_) ->
>           putStrLn $
>             prettyParseError p Nothing $ "unexpected `" ++ c:"`"

> data Pos = Pos String Int Int deriving Show

> class Pretty a where
>   pretty :: a -> String

> data BinderMode = ZeroMode | ManyMode | TypeMode deriving (Show, Eq)

> data Sort = TypeSort | KindSort deriving (Show, Eq)

> data Syntax = LambdaSyntax Pos BinderMode String Syntax Syntax
>             | IdentSyntax Pos String
>             | AppSyntax Pos BinderMode Syntax Syntax
>             | ImmediateAppSyntax Pos String [(BinderMode, String, Syntax)] Syntax Syntax Syntax
>             | NatSyntax Pos Int
>             | NatTypeSyntax Pos
>             | SortSyntax Pos Sort
>             | PiSyntax Pos BinderMode String Syntax Syntax
>             | JSyntax Pos Syntax Syntax Syntax Syntax Syntax
>             | IntersectionTypeSyntax Pos String Syntax Syntax
>             | IntersectionSyntax Pos Syntax Syntax Syntax
>             | FstSyntax Pos Syntax
>             | SndSyntax Pos Syntax
>             | EqSyntax Pos Syntax Syntax Syntax
>             | ReflSyntax Pos Syntax Syntax
>             | CastSyntax Pos Syntax Syntax Syntax
>             | ExFalsoSyntax Pos Syntax
>             deriving Show

> stxPos :: Syntax -> Pos
> stxPos stx = case stx of
>   LambdaSyntax p _ _ _ _ -> p
>   IdentSyntax p _ -> p
>   AppSyntax p _ _ _ -> p
>   ImmediateAppSyntax p _ _ _ _ _ -> p
>   NatSyntax p _ -> p
>   NatTypeSyntax p -> p
>   SortSyntax p _ -> p
>   PiSyntax p _ _ _ _ -> p
>   JSyntax p _ _ _ _ _ -> p
>   IntersectionTypeSyntax p _ _ _ -> p
>   IntersectionSyntax p _ _ _ -> p
>   FstSyntax p _ -> p
>   SndSyntax p _ -> p
>   EqSyntax p _ _ _ -> p
>   ReflSyntax p _ _ -> p
>   CastSyntax p _ _ _ -> p
>   ExFalsoSyntax p _ -> p

> prettyParams :: [(BinderMode, String, Syntax)] -> String
> prettyParams = concatMap (\(mode, x, mb_t) -> case (mode, mb_t) of
>     (ManyMode, t) -> "(" ++ x ++ ": " ++ pretty t ++ ")"
>     (ZeroMode, t) -> "{" ++ x ++ ": " ++ pretty t ++ "}"
>     (TypeMode, t) -> "<" ++ x ++ ": " ++ pretty t ++ ">"
>   )

> instance Pretty Syntax where
>   pretty stx = case stx of
>     LambdaSyntax _ ManyMode x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")-> " ++ pretty e
>     LambdaSyntax _ ZeroMode x t e -> "{" ++ x ++ ": " ++ pretty t ++ "}-> " ++ pretty e
>     LambdaSyntax _ TypeMode x t e -> "<" ++ x ++ ": " ++ pretty t ++ ">-> " ++ pretty e
>     IdentSyntax _ s -> s
>     AppSyntax _ ManyMode f a -> "(" ++ pretty f ++ ")(" ++ pretty a ++ ")"
>     AppSyntax _ ZeroMode f a -> "(" ++ pretty f ++ "){" ++ pretty a ++ "}"
>     AppSyntax _ TypeMode f a -> "(" ++ pretty f ++ ")<" ++ pretty a ++ ">"
>     ImmediateAppSyntax _ x params t v e -> "let " ++ x ++ prettyParams params ++ ": " ++ pretty t ++ " = " ++ pretty v ++ " in " ++ pretty e
>     NatSyntax _ n -> show n
>     NatTypeSyntax _ -> "Nat"
>     SortSyntax _ TypeSort -> "Type"
>     SortSyntax _ KindSort -> "Kind"
>     PiSyntax _ ManyMode x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")=> " ++ pretty e
>     PiSyntax _ ZeroMode x t e -> "{" ++ x ++ ": " ++ pretty t ++ "}=> " ++ pretty e
>     PiSyntax _ TypeMode x t e -> "<" ++ x ++ ": " ++ pretty t ++ ">=> " ++ pretty e
>     JSyntax _ a b c d e -> "J(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty c ++ ", " ++ pretty d ++ ", " ++ pretty e ++ ")"
>     IntersectionTypeSyntax _ x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")&" ++ pretty e
>     IntersectionSyntax _ a b t -> "[" ++ pretty a ++ ", " ++ pretty b ++ "; " ++ pretty t ++ "]"
>     FstSyntax _ a -> ".1(" ++ pretty a ++ ")"
>     SndSyntax _ a -> ".2(" ++ pretty a ++ ")"
>     EqSyntax _ a b t -> "(" ++ pretty a ++ ") =[" ++ pretty t ++ "] (" ++ pretty b ++ ")"
>     ReflSyntax _ a t -> "refl(" ++ pretty a ++ ", " ++ pretty t ++ ")"
>     CastSyntax _ a b eq -> "cast(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty eq ++ ", " ++ ")"
>     ExFalsoSyntax _ a -> "exfalso(" ++ pretty a ++ ")"

> data Binder where
>   Lambda :: BinderMode -> Binder
>   Pi :: BinderMode -> Binder
>   InterT :: Binder

> data Constructor0 where
>   Diamond :: Constructor0
>   Sort :: Sort -> Constructor0
>   NatT :: Constructor0
>   Nat :: Int -> Constructor0
> data Constructor1 where
>   Fst :: Constructor1 
>   Snd :: Constructor1 
>   ExFalso :: Constructor1
> data Constructor2 where 
>   App :: BinderMode -> Constructor2
>   Refl :: Constructor2
> data Constructor3 where
>   Inter :: Constructor3 
>   Eq :: Constructor3
>   Cast :: Constructor3
> data Constructor5 where 
>   J :: Constructor5

> data Term where
>   Ident :: Pos -> BinderMode -> Sort -> Int -> String -> Term
>   Binder :: Pos -> Binder -> String -> Term -> Term -> Term
>   Constructor0 :: Pos -> Constructor0 -> Term
>   Constructor1 :: Pos -> Constructor1 -> Term -> Term
>   Constructor2 :: Pos -> Constructor2 -> Term -> Term -> Term
>   Constructor3 :: Pos -> Constructor3 -> Term -> Term -> Term -> Term
>   Constructor5 :: Pos -> Constructor5 -> Term -> Term -> Term -> Term -> Term -> Term

> instance Pretty Term where
>   pretty t = case t of
>     Ident _ _ _ i x -> x ++ show i
>     Binder _ (Lambda ManyMode) x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")-> " ++ pretty e
>     Binder _ (Lambda ZeroMode) x ty e -> "{" ++ x ++ ": " ++ pretty ty ++ "}-> " ++ pretty e
>     Binder _ (Lambda TypeMode) x ty e -> "<" ++ x ++ ": " ++ pretty ty ++ ">-> " ++ pretty e
>     Binder _ (Pi ManyMode) "_" a b -> "(" ++ pretty a ++ ")=> " ++ pretty b
>     Binder _ (Pi ManyMode) x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")=> " ++ pretty e
>     Binder _ (Pi ZeroMode) "_" a b -> "{" ++ pretty a ++ "}=> " ++ pretty b
>     Binder _ (Pi ZeroMode) x ty e -> "{" ++ x ++ ": " ++ pretty ty ++ "}=> " ++ pretty e
>     Binder _ (Pi TypeMode) "_" a b -> "<" ++ pretty a ++ ">=> " ++ pretty b
>     Binder _ (Pi TypeMode) x ty e -> "<" ++ x ++ ": " ++ pretty ty ++ ">=> " ++ pretty e
>     Binder _ InterT x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")&(" ++ pretty e ++ ")"
>     Constructor0 _ Diamond -> "<>"
>     Constructor0 _ (Sort TypeSort) -> "Type"
>     Constructor0 _ (Sort KindSort) -> "Kind"
>     Constructor0 _ NatT -> "Nat"
>     Constructor0 _ (Nat n) -> show n
>     Constructor1 _ Fst a -> ".1(" ++ pretty a ++ ")"
>     Constructor1 _ Snd a -> ".2(" ++ pretty a ++ ")"
>     Constructor1 _ ExFalso a -> "exfalso(" ++ pretty a ++ ")"
>     Constructor2 _ (App ManyMode) foo bar -> "(" ++ pretty foo ++ ")(" ++ pretty bar ++ ")"
>     Constructor2 _ (App ZeroMode) foo bar -> "(" ++ pretty foo ++ "){" ++ pretty bar ++ "}"
>     Constructor2 _ (App TypeMode) foo bar -> "(" ++ pretty foo ++ ")<" ++ pretty bar ++ ">"
>     Constructor2 _ Refl a ty -> "refl(" ++ pretty a ++ ", " ++ pretty ty ++ ")"
>     Constructor3 _ Inter a b ty -> "[" ++ pretty a ++ ", " ++ pretty b ++ "; " ++ pretty ty ++ "]"
>     Constructor3 _ Eq a b ty -> "(" ++ pretty a ++ ") =[" ++ pretty ty ++ "] (" ++ pretty b ++ ")"
>     Constructor3 _ Cast a b eq -> "cast(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty eq ++ ")"
>     Constructor5 _ J eq a b ty p -> "J(" ++ pretty eq ++ ", " ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty ty ++ ", " ++ pretty p ++ ")"

> prettyContext :: [(a, Term, b)] -> String
> prettyContext gamma = intercalate ", " $ map (\(_, t, _) -> pretty t) gamma

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

> instance MonadFail Parser where
>   fail e = Parser $ \expected pos _s -> Left $ prettyParseError pos expected e

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

> parseIdent :: Parser Syntax
> parseIdent = IdentSyntax <$> position <*> identString

> data LetType = Basic | Back

> parseLet :: Parser Syntax
> parseLet = do
>   p <- position
>   _ <- exact "let"
>   _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
>   i <- patternString
>   _ <- whitespace0
>   (ident, let_type, params, t) <- do
>     mb_params <- possible parseParams
>     _ <- whitespace0
>     _ <- char ':'
>     t <- parseTerm
>     case mb_params of
>       Just params -> do
>         _ <- char '='
>         return (i, Basic, params, buildPi p params t)
>       Nothing -> do
>         op <- oneOf [exact "=", exact "<-"]
>         case op of
>           "=" -> return (i, Basic, [], t)
>           "<-" -> return (i, Back, [], t)
>           _ -> error "internal error"
>   val <- parseTerm
>   _ <- exact "in"
>   _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
>   scope <- parseTerm
>   return $ case let_type of
>     Basic -> ImmediateAppSyntax p ident params t val scope
>     Back -> AppSyntax p ManyMode val (LambdaSyntax p ManyMode ident t scope)

> buildPi :: Pos -> [(BinderMode, String, Syntax)] -> Syntax -> Syntax
> buildPi _p [] t = t
> buildPi p [(binder_mode, x, xt)] rett = PiSyntax p binder_mode x xt rett
> buildPi p ((binder_mode, x, xt):xs) rett = PiSyntax p binder_mode x xt (buildPi p xs rett)

> buildLambda :: Pos -> [(BinderMode, String, Syntax)] -> Syntax -> Syntax
> buildLambda _p [] e = e
> buildLambda p ((binder_mode, x, xt):xs) e = LambdaSyntax p binder_mode x xt (buildLambda p xs e)

> parseParens :: Parser Syntax
> parseParens = do
>   p <- position
>   _ <- char '('
>   _ <- whitespace0
>   res <- possible $ do
>     x <- identString
>     _ <- whitespace0
>     res2 <- possible $ char ':'
>     case res2 of
>       Just _ -> do
>         t <- parseTerm
>         _ <- char ')'
>         _ <- whitespace0
>         next <- oneOf [exact "&", exact "->", exact "=>"]
>         _ <- whitespace0
>         right <- parseTerm
>         case next of
>           "&" -> return $ IntersectionTypeSyntax p x t right
>           "->" -> return $ LambdaSyntax p ManyMode x t right
>           "=>" -> return $ PiSyntax p ManyMode x t right
>           _ -> error "internal error"
>       Nothing -> do
>         _ <- whitespace0
>         _ <- char ')'
>         return $ IdentSyntax p x
>   case res of
>     Just x -> return x
>     Nothing -> do
>       t <- parseTerm
>       _ <- char ')'
>       return t

> parseNat :: Parser Syntax
> parseNat = NatSyntax <$> position <*> (read <$> many (satisfy isDigit))

> parseNatType :: Parser Syntax
> parseNatType = do
>   p <- position
>   _ <- exact "Nat" -- TODO: ensure no valid identifier characters immediately following
>   return $ NatTypeSyntax p

> parseTypeSort :: Parser Syntax
> parseTypeSort = do
>   p <- position
>   _ <- exact "Type" -- TODO: ensure no valid identifier characters immediately following
>   return $ SortSyntax p TypeSort

> parseKindSort :: Parser Syntax
> parseKindSort = do
>   p <- position
>   _ <- exact "Kind" -- TODO: ensure no valid identifier characters immediately following
>   return $ SortSyntax p KindSort

> parseErased :: Parser Syntax
> parseErased = do
>   p <- position
>   _ <- char '{'
>   _ <- whitespace0
>   res <- possible $ do
>     x <- patternString
>     _ <- whitespace0
>     _ <- char ':'
>     return x
>   let x = fromMaybe "_" res
>   t <- parseTerm
>   _ <- char '}'
>   _ <- whitespace0
>   res2 <- oneOf [exact "->", exact "=>"]
>   right <- parseTerm
>   case res2 of
>     "->" -> return $ LambdaSyntax p ZeroMode x t right
>     "=>" -> return $ PiSyntax p ZeroMode x t right
>     _ -> error "internal error"

> parseAbstractType :: Parser Syntax
> parseAbstractType = do
>   p <- position
>   _ <- char '<'
>   _ <- whitespace0
>   res <- possible $ do
>     x <- patternString
>     _ <- whitespace0
>     _ <- char ':'
>     return x
>   let x = fromMaybe "_" res
>   t <- parseTerm
>   _ <- char '>'
>   _ <- whitespace0
>   res2 <- oneOf [exact "->", exact "=>"]
>   right <- parseTerm
>   case res2 of
>     "->" -> return $ LambdaSyntax p TypeMode x t right
>     "=>" -> return $ PiSyntax p TypeMode x t right
>     _ -> error "internal error"

> parseJ :: Parser Syntax
> parseJ = do
>   p <- position
>   _ <- exact "J" -- TODO: ensure no valid identifier characters immediately following
>   _ <- whitespace0
>   _ <- char '('
>   eq <- parseTerm
>   _ <- char ','
>   a <- parseTerm
>   _ <- char ','
>   b <- parseTerm
>   _ <- char ';'
>   t <- parseTerm
>   _ <- char ','
>   predicate <- parseTerm
>   _ <- char ')'
>   return $ JSyntax p eq a b t predicate

> parseRefl :: Parser Syntax
> parseRefl = do
>   p <- position
>   _ <- exact "refl" -- TODO: ensure no valid identifier characters immediately following
>   _ <- whitespace0
>   _ <- char '('
>   x <- parseTerm
>   _ <- char ','
>   t <- parseTerm
>   _ <- char ')'
>   return $ ReflSyntax p x t

> parseIntersectionType :: Parser Syntax
> parseIntersectionType = do
>   p <- position
>   _ <- char '&'
>   _ <- whitespace0
>   x <- patternString
>   _ <- whitespace0
>   _ <- char ':'
>   xt <- parseTerm
>   _ <- char '.'
>   IntersectionTypeSyntax p x xt <$> parseTerm

> parseIntersection :: Parser Syntax
> parseIntersection = do
>   p <- position
>   _ <- char '['
>   l <- parseTerm
>   _ <- char ','
>   r <- parseTerm
>   _ <- char ';'
>   _ <- whitespace0
>   t <- parseTerm -- lol, this is used in the translation, but we need to polish this later
>   _ <- whitespace0
>   _ <- char ']'
>   return $ IntersectionSyntax p l r t

> parseProjection :: Parser Syntax
> parseProjection = do
>   p <- position
>   _ <- char '.'
>   n <- oneOf [char '1', char '2']
>   _ <- whitespace0
>   _ <- char '('
>   i <- parseTerm
>   _ <- char ')'
>   case n of
>     '1' -> return $ FstSyntax p i
>     '2' -> return $ SndSyntax p i
>     _ -> error "internal error"

> parseCast :: Parser Syntax
> parseCast = do
>   p <- position
>   _ <- exact "cast"
>   _ <- whitespace0
>   _ <- char '('
>   a <- parseTerm
>   _ <- char ','
>   b <- parseTerm
>   _ <- char ','
>   t <- parseTerm
>   _ <- char ')'
>   return $ CastSyntax p a b t

> parseExFalso :: Parser Syntax
> parseExFalso = do
>   p <- position
>   _ <- exact "exfalso" -- TODO: ensure no valid identifier characters immediately following
>   _ <- whitespace0
>   _ <- char '('
>   a <- parseTerm
>   _ <- char ')'
>   return $ ExFalsoSyntax p a

> parseTermNoPostfix :: Parser Syntax
> parseTermNoPostfix = do
>   _ <- whitespace0
>   t <- oneOf
>     [ parseParens
>     , parseErased
>     , parseAbstractType
>     , parseIntersectionType
>     , parseIntersection
>     , parseProjection
>     , parseNat
>     , parseLet
>     , parseNatType
>     , parseTypeSort
>     , parseKindSort
>     , parseJ
>     , parseRefl
>     , parseCast
>     , parseExFalso
>     , parseIdent
>     ]
>   _ <- whitespace0
>   return t

> data Postfix = AppPostfix Pos Syntax
>              | ErasedAppPostfix Pos Syntax
>              | AbstractTypeAppPostfix Pos Syntax
> --           | MonoidPostfix Pos [Syntax]
>              | ApostrophePostfix Pos Syntax
>              | EqTypePostfix Pos Syntax Syntax
>              | FuncTypePostfix Pos Syntax
>              | IntersectionTypePostfix Pos Syntax

> parseTerm :: Parser Syntax
> parseTerm = do
>   t <- parseTermNoPostfix
>   args <- many0 $ whitespace0 *> oneOf
>     [ do
>       p2 <- position
>       _ <- char '('
>       arg <- parseTerm
>       _ <- char ')'
>       return $ AppPostfix p2 arg
>     , do
>       p2 <- position
>       _ <- char '{'
>       arg <- parseTerm
>       _ <- char '}'
>       return $ ErasedAppPostfix p2 arg
>     , do
>       p2 <- position
>       _ <- char '<'
>       arg <- parseTerm
>       _ <- char '>'
>       return $ AbstractTypeAppPostfix p2 arg
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
>       ApostrophePostfix p2 <$> parseTerm
>     , do
>       p2 <- position
>       _ <- char '='
>       _ <- whitespace0
>       _ <- char '['
>       ty <- parseTerm
>       _ <- char ']'
>       flip (EqTypePostfix p2) ty <$> parseTerm
>     , do
>       p2 <- position
>       _ <- exact "=>"
>       FuncTypePostfix p2 <$> parseTerm
>     , do
>       p2 <- position
>       _ <- char '&'
>       IntersectionTypePostfix p2 <$> parseTerm
>     ]
>   let out = case args of
>         [] -> t
>         _ -> foldl' (\b a-> case a of
>             AppPostfix p2 arg -> AppSyntax p2 ManyMode b arg
>             ErasedAppPostfix p2 arg -> AppSyntax p2 ZeroMode b arg
>             AbstractTypeAppPostfix p2 arg -> AppSyntax p2 TypeMode b arg
>             {- MonoidPostfix p2 terms ->
>               foldr (\term so_far->
>                   AppSyntax p2
>                       (AppSyntax p2
>                           (AccessSyntax (stxPos b) b "Has")
>                         term)
>                     so_far
>                 ) (AccessSyntax (stxPos b) b "Empty") terms -}
>             ApostrophePostfix p2 rhs -> AppSyntax p2 ManyMode b rhs
>             EqTypePostfix p2 rhs ty -> EqSyntax p2 b rhs ty
>             FuncTypePostfix p2 rhs -> PiSyntax p2 ManyMode "_" b rhs
>             IntersectionTypePostfix p2 rhs -> IntersectionTypeSyntax p2 "_" b rhs
>           ) t args
>   _ <- whitespace0
>   return out

> parseParams :: Parser [(BinderMode, String, Syntax)]
> parseParams = many $ do
>     res <- oneOf [char '(', char '<', char '{']
>     _ <- whitespace0
>     param <- patternString
>     _ <- whitespace0
>     _ <- char ':'
>     case res of
>       '(' -> do
>         t <- parseTerm
>         _ <- char ')'
>         return (ManyMode, param, t)
>       '<' -> do
>         t <- parseTerm
>         _ <- char '>'
>         return (TypeMode, param, t)
>       '{' -> do
>         t <- parseTerm
>         _ <- char '}'
>         return (ZeroMode, param, t)
>       _ -> error "internal error"

> parseDecl :: Parser (Either (String, (Syntax, Syntax)) [String])
> parseDecl = do
>   p <- position
>   _ <- exact "def"
>   _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
>   name <- identString
>   mb_not_func <- possible (whitespace0 >> char ':')
>   case mb_not_func of
>     Just _ -> do
>       t <- parseTerm
>       _ <- char '='
>       body <- parseTerm
>       return $ Left (name, (t, body))
>     Nothing -> do
>       params <- parseParams
>       _ <- whitespace0
>       _ <- char ':'
>       t <- parseTerm
>       _ <- char '='
>       body <- parseTerm
>       let body2 = buildLambda p params body
>       return $ Left (name, (t, body2))

> parseFile :: Parser (Map.Map String (Syntax, Syntax), [[String]])
> parseFile = do
>   let parser = many $ whitespace0 *>
>         parseDecl <* whitespace0
>   (decls, imports) <- fmap partitionEithers parser
>   return (Map.fromList decls, imports)

> sortOf :: Map.Map String (Int, BinderMode, Sort) -> Term -> Sort
> sortOf renames (Ident _ _ _ _ s) = case Map.lookup s renames of
>   Just (_, _, sort) -> sort
>   Nothing -> error "internal error"
> sortOf renames (Binder _ (Pi _) _ _ body) = sortOf renames body
> sortOf _renames (Binder _ InterT _ _ _) = TypeSort
> sortOf _renames (Constructor0 _ NatT) = TypeSort
> sortOf _renames (Constructor0 _ (Sort TypeSort)) = KindSort
> sortOf _renames (Constructor3 _ Eq _ _ _) = TypeSort
> sortOf _renames _term = error "internal error"

> translate :: Int -> Map.Map String (Int, BinderMode, Sort) -> [Term] -> Syntax -> Either String Term
> translate index renames psi t =
>   let tr = translate in
>   case t of
>     LambdaSyntax p binder_mode param ty body -> do
>       ty2 <- tr index renames [] ty
>       body2 <- tr (index + 1) (Map.insert param (index, binder_mode, sortOf renames ty2) renames) (tail psi) body
>       return $ Binder p (Lambda binder_mode) param ty2 body2
>     IdentSyntax p ('#':name) -> return $ Ident p ManyMode TypeSort 0 $ '#':name
>     IdentSyntax p name ->
>       case Map.lookup name renames of
>         Just (i, bm, sort) -> return $ Ident p bm sort (index - i - 1) name
>         Nothing -> Left $ prettyParseError p Nothing $ "undefined variable `" ++ name ++ "`"
>     AppSyntax p bm foo bar -> do
>       bar2 <- tr index renames [] bar
>       foo2 <- tr index renames (bar2:psi) foo
>       return $ Constructor2 p (App bm) foo2 bar2
>     ImmediateAppSyntax p x params ty v e -> do
>       ty2 <- tr index renames [] ty
>       v2 <- tr index renames [] (buildLambda p params v)
>       let binder_mode = letBinderMode v2
>       e2 <- tr (index + 1) (Map.insert x (index, binder_mode, sortOf renames v2) renames) psi e
>       return $ Constructor2 p (App binder_mode) (Binder p (Lambda binder_mode) x ty2 e2) v2
>     NatSyntax p n -> return $ Constructor0 p (Nat n)
>     NatTypeSyntax p -> return $ Constructor0 p NatT
>     SortSyntax p s -> return $ Constructor0 p (Sort s)
>     PiSyntax p binder_mode param ty body -> do
>       ty2 <- tr index renames [] ty
>       body2 <- tr (index + 1) (Map.insert param (index, binder_mode, sortOf renames ty2) renames) psi body
>       return $ Binder p (Pi binder_mode) param ty2 body2
>     JSyntax p eq a b c predicate -> do
>       eq2 <- tr index renames [] eq
>       a2 <- tr index renames [] a
>       b2 <- tr index renames [] b
>       c2 <- tr index renames [] c
>       predicate2 <- tr index renames [] predicate
>       return $ Constructor5 p J eq2 a2 b2 c2 predicate2
>     EqSyntax p a b ty -> do
>       a2 <- tr index renames [] a
>       b2 <- tr index renames [] b
>       ty2 <- tr index renames [] ty
>       return $ Constructor3 p Eq a2 b2 ty2
>     ReflSyntax p x ty -> do
>       x2 <- tr index renames [] x
>       ty2 <- tr index renames [] ty
>       return $ Constructor2 p Refl x2 ty2
>     IntersectionTypeSyntax p x xt r -> do
>       xt2 <- tr index renames [] xt
>       r2 <- tr (index + 1) (Map.insert x (index, ZeroMode, TypeSort) renames) [] r
>       return $ Binder p InterT x xt2 r2
>     IntersectionSyntax p a b ty -> do
>       a2 <- tr index renames psi a
>       case ty of
>         IntersectionTypeSyntax _ x xt r -> do
>           b2 <- tr (index + 1) (Map.insert x (index, ZeroMode, TypeSort) renames) psi b
>           xt2 <- tr index renames [] xt
>           r2 <- tr (index + 1) (Map.insert x (index, ZeroMode, TypeSort) renames) [] r
>           return $ Constructor3 p Inter a2 b2 $ Binder p InterT x xt2 r2
>         _ -> do
>           b2 <- tr (index + 1) renames psi b
>           ty2 <- tr index renames psi ty
>           return $ Constructor3 p Inter a2 b2 ty2
>     FstSyntax p a -> do
>       a2 <- tr index renames psi a
>       return $ Constructor1 p Fst a2
>     SndSyntax p a -> do
>       a2 <- tr index renames psi a
>       return $ Constructor1 p Snd a2
>     CastSyntax p a b ty -> do
>       a2 <- tr index renames psi a
>       b2 <- tr index renames psi b
>       ty2 <- tr index renames psi ty
>       return $ Constructor3 p Cast a2 b2 ty2
>     ExFalsoSyntax p a -> Constructor1 p ExFalso <$> tr index renames psi a

> shift :: Int -> Int -> Term -> Term
> shift depth amt term = 
>   let sh d = shift d amt in
>   case term of
>     Ident p bm s i str | i >= depth -> Ident p bm s (i + amt) str
>     Ident p bm s i str -> Ident p bm s i str
>     Binder p b x xt body -> Binder p b x (sh depth xt) (sh (depth + 1) body)
>     Constructor0 p k -> Constructor0 p k
>     Constructor1 p k a -> Constructor1 p k (sh depth a)
>     Constructor2 p k a b -> Constructor2 p k (sh depth a) (sh depth b)
>     Constructor3 p Inter a b t -> Constructor3 p Inter (sh depth a) (sh (depth+1) b) (sh depth t)
>     Constructor3 p k a b c -> Constructor3 p k (sh depth a) (sh depth b) (sh depth c)
>     Constructor5 p k a b c d e -> Constructor5 p k (sh depth a) (sh depth b) (sh depth c) (sh depth d) (sh depth e)

> inc :: Term -> Term
> inc = shift 0 1
> dec :: Term -> Term
> dec = shift 0 (-1)

> subst :: Term -> Int -> Term -> Term
> subst term depth new = case term of
>   Ident _ _ _ i _ -> if depth == i then new else term
>   Binder p b x xt body -> Binder p b x (subst xt depth new) (subst body (depth + 1) (inc new))
>   Constructor0 p k -> Constructor0 p k
>   Constructor1 p k a -> Constructor1 p k (subst a depth new)
>   Constructor2 p k foo bar -> Constructor2 p k (subst foo depth new) (subst bar depth new)
>   Constructor3 p Inter a b t -> Constructor3 p Inter (subst a depth new) (subst b (depth + 1) (inc new)) (subst t depth new)
>   Constructor3 p k a b c -> Constructor3 p k (subst a depth new) (subst b depth new) (subst c depth new)
>   Constructor5 p k a b c d e -> Constructor5 p k (subst a depth new) (subst b depth new) (subst c depth new) (subst d depth new) (subst e depth new)

> identity :: Pos -> Term
> identity p = Binder p (Lambda ManyMode) "$x" (Constructor0 p Diamond) $ Ident p ManyMode TypeSort 0 "$x"

> alphaEq :: Term -> Term -> Bool
> alphaEq a b = case (a, b) of
>   (Ident _ _ _ i _, Ident _ _ _ j _) -> i == j
>   (Constructor0 _ NatT, Constructor0 _ NatT) -> True
>   (Constructor0 _ (Sort s1), Constructor0 _ (Sort s2)) -> s1 == s2
>   (Binder _ (Pi mode1) _ xt body1, Binder _ (Pi mode2) _ yt body2) -> mode1 == mode2 && alphaEq xt yt && alphaEq body1 body2
>   (Binder _ (Lambda mode1) _ xt body1, Binder _ (Lambda mode2) _ yt body2) -> mode1 == mode2 && alphaEq xt yt && alphaEq body1 body2
>   (Constructor2 _ (App mode1) foo1 bar1, Constructor2 _ (App mode2) foo2 bar2) -> mode1 == mode2 && alphaEq foo1 foo2 && alphaEq bar1 bar2
>   (Constructor0 _ (Nat n), Constructor0 _ (Nat m)) -> n == m
>   (Constructor3 _ Eq l1 r1 t1, Constructor3 _ Eq l2 r2 t2) -> alphaEq l1 l2 && alphaEq r1 r2 && alphaEq t1 t2
>   (Binder _ InterT _ xt t1, Binder _ InterT _ yt t2) -> alphaEq xt yt && alphaEq t1 t2
>   (Constructor0 _ Diamond, Constructor0 _ Diamond) -> True
>   (Constructor1 _ ExFalso e1, Constructor1 _ ExFalso e2) -> alphaEq e1 e2
>   (Constructor1 _ Fst i1, Constructor1 _ Fst i2) -> alphaEq i1 i2
>   (Constructor1 _ Snd i1, Constructor1 _ Snd i2) -> alphaEq i1 i2
>   (Constructor2 _ Refl e1 t1, Constructor2 _ Refl e2 t2) -> alphaEq e1 e2 && alphaEq t1 t2
>   (Constructor3 _ Inter l1 r1 t1, Constructor3 _ Inter l2 r2 t2) -> alphaEq l1 l2 && alphaEq r1 r2 && alphaEq t1 t2
>   (Constructor5 _ J eq1 a1 b1 t1 p1, Constructor5 _ J eq2 a2 b2 t2 p2) -> alphaEq eq1 eq2 && alphaEq a1 a2 && alphaEq b1 b2 && alphaEq t1 t2 && alphaEq p1 p2
>   _ -> False

> termEq :: [(BinderMode, Term, Maybe Term)] -> Term -> Term -> Bool
> termEq gamma a b = alphaEq (erase $ normalize (normalizeContext gamma) a) (erase $ normalize (normalizeContext gamma) b)

> erase :: Term -> Term
> erase term = case term of
>   Ident {} -> term
>   Binder _ (Lambda ZeroMode) _ _ body -> dec $ erase body
>   Binder p (Lambda ManyMode) x _ body -> Binder p (Lambda ManyMode) x (Constructor0 p Diamond) $ erase body
>   Binder p (Lambda TypeMode) x xt body -> Binder p (Lambda TypeMode) x (erase xt) $ erase body
>   Binder p (Pi m) x xt body -> Binder p (Pi m) x (erase xt) $ erase body
>   Binder p InterT x xt r -> Binder p InterT x (erase xt) $ erase r
>   Constructor0 {} -> term
>   Constructor1 p ExFalso e -> Constructor1 p ExFalso $ erase e
>   Constructor1 _ Fst i -> erase i
>   Constructor1 _ Snd i -> erase i
>   Constructor2 _ (App ZeroMode) foo _ -> erase foo
>   Constructor2 p (App m) foo bar -> Constructor2 p (App m) (erase foo) (erase bar)
>   Constructor2 p Refl _ _ -> identity p
>   Constructor3 _ Inter l _ _ -> erase l
>   Constructor3 p Eq a b t -> Constructor3 p Eq (erase a) (erase b) (erase t)
>   Constructor3 _ Cast a _ _ -> erase a
>   Constructor5 _ J e _ _ _ _ -> erase e

> normalizeContext :: [(BinderMode, Term, Maybe Term)] -> [(BinderMode, Term, Maybe Term)]
> normalizeContext gamma = case gamma of
>   [] -> []
>   (a, b, Nothing):rest -> (a, b, Nothing):normalizeContext rest
>   (a, b, Just v):rest -> let g = normalizeContext rest in (a, b, Just (normalize g v)) : g

> idx :: [a] -> Int -> Maybe a
> idx xs i = case xs of
>   [] -> Nothing
>   (x:rest) -> if i == 0 then Just x else idx rest (i - 1)

> normalize :: [(BinderMode, Term, Maybe Term)] -> Term -> Term
> normalize gamma term = case term of
>   Ident _ _ _ i _ -> case gamma `idx` i of
>     Just (_, _, Just v) -> shift 0 i v
>     _ -> term
>   Constructor2 p (App m) foo bar -> 
>     let foo2 = normalize gamma foo in
>     let bar2 = normalize gamma bar in
>     case foo2 of
>       Binder _ (Lambda _) _ _ body -> normalize gamma $ dec $ subst body 0 (inc bar2)
>       Constructor5 _ J _ (Constructor2 _ Refl _ _) _ _ _ -> bar2
>       _ -> Constructor2 p (App m) foo2 bar2
>   Constructor1 p Fst e ->
>     let e2 = normalize gamma e in
>     case e2 of
>       Constructor3 _ Inter l _ _ -> l
>       _ -> Constructor1 p Fst e2
>   Constructor1 p Snd e ->
>     let e2 = normalize gamma e in
>     case e2 of
>       Constructor3 _ Inter _ r _ -> r
>       _ -> Constructor1 p Snd e2
>   Binder p k x t b -> Binder p k x (normalize gamma t) (normalize ((ManyMode, t, Nothing):gamma) b) -- first two components of the triple don't matter
>   Constructor0 p k -> Constructor0 p k
>   Constructor1 p k a -> Constructor1 p k $ normalize gamma a
>   Constructor2 p k a b ->
>     let a2 = normalize gamma a in
>     let b2 = normalize gamma b in
>     Constructor2 p k a2 b2
>   Constructor3 p k a b c ->
>     let a2 = normalize gamma a in
>     let b2 = normalize gamma b in
>     let c2 = normalize gamma c in
>     Constructor3 p k a2 b2 c2
>   Constructor5 p k eq a b c predicate -> 
>     let eq2 = normalize gamma eq in
>     let a2 = normalize gamma a in
>     let b2 = normalize gamma b in
>     let c2 = normalize gamma c in
>     let predicate2 = normalize gamma predicate in
>     Constructor5 p k eq2 a2 b2 c2 predicate2

> letBinderMode :: Term -> BinderMode
> letBinderMode ty = case ty of
>   Ident _p bm _ _i _n -> bm
>   Binder _ (Pi _) _ _ body -> letBinderMode body
>   Binder _ (Lambda _) _ _ body -> letBinderMode body
>   Binder _ InterT _ _ _ -> ZeroMode
>   Constructor0 _ (Nat _) -> ManyMode
>   Constructor0 _ NatT -> ZeroMode
>   Constructor0 _ (Sort _) -> ZeroMode
>   Constructor0 _ Diamond -> ZeroMode
>   Constructor1 _ Fst i -> letBinderMode i
>   Constructor1 _ Snd i -> letBinderMode i
>   Constructor1 _ ExFalso _ -> ManyMode
>   Constructor2 _ (App _) foo _ -> letBinderMode foo
>   Constructor2 _ Refl _ _ -> ManyMode
>   Constructor3 _ Eq _ _ _ -> ZeroMode
>   Constructor3 _ Inter l _ _ -> letBinderMode l
>   Constructor3 _ Cast _ _ _ -> ManyMode
>   Constructor5 _ J _ _ _ _ _ -> ManyMode

> funcTypeCodomain :: BinderMode -> Sort
> funcTypeCodomain ManyMode = TypeSort
> funcTypeCodomain TypeMode = KindSort
> funcTypeCodomain ZeroMode = TypeSort

> infer :: Maybe Term -> [(BinderMode, Term, Maybe Term)] -> Term -> Either String Term
> infer arg gamma term = case term of
>   Constructor0 p (Sort TypeSort) -> return $ Constructor0 p (Sort KindSort)
>   Constructor0 _ (Sort KindSort) -> undefined
>   Ident _ _ _ i x -> do
>     case gamma `idx` i of
>       Just (_, t, _) -> return $ shift 0 i t
>       _ -> Left $ "unknown identifier `" ++ x ++ "` (" ++ show i ++ ")"
>   Binder p (Pi mode) _ xt body -> do
>     ak <- infer Nothing gamma xt
>     let b_gamma = (mode, inc xt, Nothing): gamma
>     bt <- infer Nothing b_gamma body
>     if termEq b_gamma bt (Constructor0 p $ Sort $ funcTypeCodomain mode) then
>       case ak of
>         Constructor0 _ (Sort KindSort) | mode == ManyMode ->
>           Left "type error, many-mode functions can't return erased things"
>         _ -> return bt
>     else Left $ show p ++ " type mismatch, due to " ++ show mode ++ ", expected a codomain of kind " ++ pretty (Constructor0 p $ Sort $ funcTypeCodomain mode) ++ ", got " ++ pretty bt
>   Binder p (Lambda mode) x xt body -> do -- TODO: check that zero-mode lambdas don't mention their parameters in unerased expressions
>     let gamma2 = (mode, inc xt, arg):gamma
>     body_t <- infer Nothing gamma2 body
>     let ty = Binder p (Pi mode) x xt body_t
>     k <- infer Nothing gamma ty
>     if termEq gamma k (Constructor0 p $ Sort $ funcTypeCodomain mode) then
>       return ty
>     else Left $ "type mismatch, expected a codomain of kind `" ++ pretty (Constructor0 p $ Sort $ funcTypeCodomain mode) ++ "`, got `" ++ pretty k ++ "`"
>   Constructor2 p (App mode) foo bar -> do
>     bar_t <- infer Nothing gamma bar
>     foo_t <- infer (Just bar) gamma foo
>     let foo_t_norm = normalize (normalizeContext gamma) foo_t
>     case foo_t_norm of
>       Binder _ (Pi mode2) _ xt body_t ->
>         if mode == mode2 then do
>           if termEq gamma xt bar_t then
>               return $ dec $ subst body_t 0 $ inc bar
>           else Left $ "type mismatch, expected a `" ++ pretty xt ++ "`, got `" ++ pretty bar ++ ": " ++ pretty bar_t ++ "` at " ++ show p
>         else Left $ "mode mismatch, expected " ++ show mode2 ++ ", got " ++ show mode
>       _ -> Left $ show p ++ " expected function, got " ++ pretty foo_t
>   Constructor0 p NatT -> return $ Constructor0 p (Sort TypeSort)
>   Constructor0 p (Nat _) -> return $ Constructor0 p NatT
>   Binder p InterT _x a b -> do
>     ak <- infer Nothing gamma a
>     let b_gamma = (ZeroMode, inc a, Nothing):gamma
>     bk <- infer Nothing b_gamma b
>     if termEq gamma ak (Constructor0 p $ Sort TypeSort) && termEq b_gamma bk (Constructor0 p $ Sort TypeSort) then do
>       return $ Constructor0 p (Sort TypeSort)
>      else Left $ "type mismatch, expected two types for the intersection type, got `" ++ pretty ak ++ "` and `" ++ pretty bk ++ "`"
>   Constructor3 p Inter l r t -> do
>     l_t <- infer Nothing gamma l
>     let l2 = inc l
>     r_t <- infer Nothing gamma $ dec $ subst r 0 $ inc l
>     _ <- infer Nothing gamma t
>     if termEq gamma l2 r then do
>       let pse = normalize (normalizeContext gamma) t -- TODO: find the better, more general spot to do this evaluation
>       case pse of
>         Binder _ InterT x l_t_2 r_t_2 ->
>           if termEq gamma l_t l_t_2 && termEq gamma r_t (dec $ subst r_t_2 0 $ inc l) then
>             return t
>           else Left $ "type mismatch, Intersection equatees don't match type annotation (`(" ++ x ++ ": " ++ pretty l_t ++ ") & (" ++ pretty r_t ++ ")` should convert to `(" ++ x ++ ": " ++ pretty l_t_2 ++ ") & (" ++ pretty (dec $ subst r_t_2 0 $ inc l) ++ ")`)"
>         _ -> Left $ "type error, Intersections must be given intersection types (`" ++ pretty t ++ "` might not be an intersection type)"
>     else Left $ show p ++ " type mismatch, Intersection equatees aren't definitionally equal (`" ++ pretty l ++ "` != `" ++ pretty r ++ "`)"
>   Constructor1 _ Fst i -> do
>     i_t <- infer Nothing gamma i
>     let pse = normalize (normalizeContext gamma) i_t -- TODO: find the better, more general spot to do this evaluation
>     case pse of
>       Binder _ InterT _ l _ -> return l
>       _ -> Left $ "type error, Fst argument must be an intersection, but instead it is `" ++ pretty i ++ ": " ++ pretty i_t ++ "` (" ++ pretty pse ++ ")"
>   Constructor1 p Snd i -> do
>     i_t <- infer Nothing gamma i
>     let pse = normalize (normalizeContext gamma) i_t -- TODO: find the better, more general spot to do this evaluation
>     case pse of
>       Binder _ InterT _ _ r -> return $ dec $ subst r 0 (Constructor1 p Fst $ inc i)
>       _ -> Left $ "type error, Snd argument must be an intersection, but instead has type `" ++ pretty i_t ++ "`"
>   Constructor5 p J eq a b c predicate -> do
>     eq_t <- infer Nothing gamma eq
>     a_t <- infer Nothing gamma a
>     b_t <- infer Nothing gamma b
>     if termEq gamma a_t b_t then
>       case eq_t of
>         Constructor3 _ Eq l r t | termEq gamma a l && termEq gamma b r && termEq gamma a_t t -> do
>           if termEq gamma c t then do
>             pred_t <- infer Nothing gamma predicate
>             case pred_t of
>               Binder _ (Pi TypeMode) var_name param_t (Binder _ (Pi TypeMode) _var2_name (Constructor3 _ Eq l2 r2 t2) (Constructor0 _ (Sort TypeSort))) | termEq gamma param_t t && termEq gamma (inc a) l2 && termEq gamma (Ident p TypeMode TypeSort 0 var_name) r2 && termEq gamma (inc t) t2-> do
>                 return $ Binder p (Pi ManyMode) "_" (Constructor2 p (App TypeMode) (Constructor2 p (App TypeMode) predicate a) (Constructor2 p Refl a t)) (Constructor2 p (App TypeMode) (Constructor2 p (App TypeMode) (inc predicate) (inc b)) $ inc eq)
>               Binder _ (Pi TypeMode) var_name param_t (Binder _ (Pi TypeMode) _var2_name (Constructor3 _ Eq l2 r2 t2) (Constructor0 _ (Sort TypeSort))) ->
>                 Left $ "param_t = t: " ++ show (termEq gamma param_t t) ++ ", a = l2: " ++ show (termEq gamma (inc a) l2) ++ " (" ++ pretty (inc a) ++ ", " ++ pretty l2 ++ "), " ++ var_name ++ " = r2: " ++ show (termEq gamma (Ident p TypeMode TypeSort 0 var_name) r2) ++ ", t = t2: " ++ show (termEq gamma (inc t) t2)
>               _ -> Left $ "type error, the predicate of J has an invalid type (`" ++ pretty pred_t ++ "`)"   
>           else Left $ "type error, the fourth argument of J must be the type of the first two arguments (`" ++ pretty t ++ "` != `" ++ pretty c ++ "`)"
>         _ -> Left $ "type error, the first three arguments of J don't form a valid equation (`" ++ pretty eq_t ++ "`, `" ++ pretty a_t ++ "`, `" ++ pretty b_t ++ "`)"
>     else Left $ "type mismatch, J equatees must have the same type (`" ++ pretty a_t ++ "` and `" ++ pretty b_t ++ "` are not equal)"
>   Constructor3 p Eq l r t -> do
>     l_t <- infer Nothing gamma l
>     r_t <- infer Nothing gamma r
>     if termEq gamma l_t r_t && termEq gamma l_t t then
>       return $ Constructor0 p (Sort TypeSort)
>     else Left $ "type mismatch, Eq equatees must have the same type (`" ++ pretty l_t ++ "` and `" ++ pretty r_t ++ "` should convert to `" ++ pretty t ++ "`)"
>   Constructor2 p Refl a t -> do
>     a_t <- infer Nothing gamma a
>     if termEq gamma a_t t then
>       return $ Constructor3 p Eq a a t
>     else Left $ "type mismatch, Refl first argument must have second argument as type (`" ++ pretty a_t ++ "` != `" ++ pretty t ++ "`)"
>   Constructor3 p Cast a b eq -> do
>     a_t <- infer Nothing gamma a
>     b_t <- infer Nothing gamma b
>     case b_t of
>       Binder _ InterT _ l _ | termEq gamma a_t l -> do
>         eq_t <- infer Nothing gamma eq
>         case eq_t of
>           Constructor3 _ Eq l2 r2 t2 | termEq gamma a l2 && termEq gamma (Constructor1 p Fst b) r2 && termEq gamma a_t t2 -> do
>             return b_t
>           _ -> Left $ "type error, Cast third argument must be an equation (but it's a `" ++ pretty eq_t ++ "`)"
>       _ -> Left $ "type error, Cast second argument must be an intersection, but instead has type `" ++ pretty b_t ++ "`"
>   Constructor0 p Diamond -> return $ Constructor0 p (Sort TypeSort)
>   Constructor1 p ExFalso a -> do
>     a_t <- infer Nothing gamma a
>     if termEq gamma a_t (Constructor3 p Eq (ctt p) (cff p) (cBool p)) then
>       return $ Binder p (Pi ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Ident p ZeroMode KindSort 0 "t")
>     else Left $ "type error, ExFalso argument must be a proof that true equals false, but instead is a `" ++ pretty a_t ++ "`"

> cBool :: Pos -> Term
> cBool p = Binder p (Pi ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Pi ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Pi ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ZeroMode KindSort 2 "t")))
> ctt :: Pos -> Term
> ctt p = Binder p (Lambda ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Lambda ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Lambda ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ManyMode TypeSort 1 "x")))
> cff :: Pos -> Term
> cff p = Binder p (Lambda ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Lambda ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Lambda ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ManyMode TypeSort 0 "y")))

> captures :: [Int] -> Int -> Term -> Set.Set Int
> captures caps depth t = case t of
>   Binder _ (Lambda _) _ _ body -> Set.map (\n->n-1) $ captures caps (depth + 1) body
>   Ident _ _ _ i _ ->
>     if i < depth then Set.empty else Set.singleton i
>   Constructor2 _ (App ManyMode) foo bar -> captures caps depth foo `Set.union` captures caps depth bar
>   Constructor2 _ (App ZeroMode) foo _bar -> captures caps depth foo
>   Constructor3 _ Inter l _ _ -> captures caps depth l
>   Constructor1 _ Fst i -> captures caps depth i
>   Constructor1 _ Snd i -> captures caps depth i
>   _ -> Set.empty

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

> codegen :: [Int] -> [Int] -> Term -> [Word8]
> codegen caps kcaps t = case t of
>   Binder _ (Lambda ManyMode) _ _ body -> 
>     let body_caps = Set.toAscList $ captures [] 1 body in
>     let body_cap_indices = map (\n->fromMaybe (-1) (elemIndex (n-1) caps) + 1) body_caps in
>     let body_ops = codegen body_caps kcaps body in
>     concatMap capOp (reverse body_cap_indices) ++ lamOp (length body_ops + 1) ++ body_ops ++ retOp
>   Binder _ (Lambda ZeroMode) _ _ body -> codegen caps kcaps body
>   Ident _ _ _ i _ ->
>     case elemIndex i caps of
>       Just index -> varOp (index + 1)
>       Nothing -> varOp 0
>   Constructor2 _ (App ManyMode) foo bar -> 
>     let bar_caps = Set.toAscList $ captures [] 0 bar in
>     codegen caps bar_caps foo ++ codegen caps kcaps bar ++ concatMap capOp kcaps ++ appOp
>   Constructor2 _ (App ZeroMode) foo _bar -> codegen caps kcaps foo
>   Constructor0 _ (Nat n) -> litOp n
>   Constructor5 _ J _ _ _ _ _ -> lamOp 3 ++ varOp 0 ++ retOp -- J compiles to the unerased identity function
>   Constructor2 _ Refl _ _ -> lamOp 3 ++ varOp 0 ++ retOp -- Refl compiles to the unerased identity function
>   Constructor3 _ Inter l _ _ -> codegen caps kcaps l
>   Constructor1 _ Fst i -> codegen caps kcaps i
>   Constructor1 _ Snd i -> codegen caps kcaps i
>   Constructor3 _ Cast a _ _ -> codegen caps kcaps a
>   _ -> undefined