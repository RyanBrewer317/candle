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
> import Data.Maybe (fromMaybe, fromJust)
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
>         let res = translate 0 Map.empty [] t
>         case res of
>           Left err -> putStrLn err
>           Right t2 -> do
>             case infer Nothing [] [] t2 of
>               Left err -> putStrLn err
>               Right _t3 -> do
>                 let bytecode = codegen [] [] t2 ++ [29, 0]
>                 h_out <- openFile "bin.fvm" WriteMode
>                 B.hPut h_out $ B.pack bytecode
>                 hClose h_out
>                 _ <- system "vendor/fvm bin.fvm"
>                 return ()
>       Right (_, p, c:_) ->
>         putStrLn $
>           prettyParseError p Nothing $ "unexpected `" ++ c:"`"
>     main

> data Pos = Pos String Int Int deriving Show

> class Pretty a where
>   pretty :: a -> String

> data BinderMode = ZeroMode | ManyMode deriving (Show, Eq)

> data Sort = TypeSort | KindSort deriving (Show, Eq)

> data Syntax = LambdaSyntax Pos BinderMode String (Maybe Syntax) Syntax
>             | IdentSyntax Pos String
>             | AppSyntax Pos BinderMode Syntax Syntax
>             | ImmediateAppSyntax Pos String [(BinderMode, String, Maybe Syntax)] Syntax Syntax
>             | NatSyntax Pos Int
>             | NatTypeSyntax Pos
>             | SortSyntax Pos Sort
>             | PiSyntax Pos BinderMode String Syntax Syntax
>             | JSyntax Pos Syntax Syntax Syntax Syntax Syntax
>             | IntersectionTypeSyntax Pos String Syntax Syntax
>             | IntersectionSyntax Pos Syntax Syntax String Syntax Syntax
>             | FstSyntax Pos Syntax
>             | SndSyntax Pos Syntax
>             | EqSyntax Pos Syntax Syntax Syntax
>             | ReflSyntax Pos Syntax Syntax
>             | InterEqSyntax Pos Syntax Syntax Syntax Syntax
>             | CastSyntax Pos Syntax Syntax Syntax
>             | ExFalsoSyntax Pos Syntax
>             deriving Show

> stxPos :: Syntax -> Pos
> stxPos stx = case stx of
>   LambdaSyntax p _ _ _ _ -> p
>   IdentSyntax p _ -> p
>   AppSyntax p _ _ _ -> p
>   ImmediateAppSyntax p _ _ _ _ -> p
>   NatSyntax p _ -> p
>   NatTypeSyntax p -> p
>   SortSyntax p _ -> p
>   PiSyntax p _ _ _ _ -> p
>   JSyntax p _ _ _ _ _ -> p
>   IntersectionTypeSyntax p _ _ _ -> p
>   IntersectionSyntax p _ _ _ _ _ -> p
>   FstSyntax p _ -> p
>   SndSyntax p _ -> p
>   EqSyntax p _ _ _ -> p
>   ReflSyntax p _ _ -> p
>   InterEqSyntax p _ _ _ _ -> p
>   CastSyntax p _ _ _ -> p
>   ExFalsoSyntax p _ -> p

> prettyParams :: [(BinderMode, String, Maybe Syntax)] -> String
> prettyParams = concatMap (\(mode, x, mb_t) -> case (mode, mb_t) of
>     (ManyMode, Just t) -> "(" ++ x ++ ": " ++ pretty t ++ ")"
>     (ManyMode, Nothing) -> "(" ++ x ++ ")"
>     (_,  Just t) -> "<" ++ x ++ ": " ++ pretty t ++ ">"
>     (_, Nothing) -> "<" ++ x ++ ">"
>   )

> instance Pretty Syntax where
>   pretty stx = case stx of
>     LambdaSyntax _ ManyMode x (Just t) e -> "(" ++ x ++ ": " ++ pretty t ++ ")-> " ++ pretty e
>     LambdaSyntax _ ManyMode x Nothing e -> "(" ++ x ++ ")-> " ++ pretty e
>     LambdaSyntax _ _ x (Just t) e -> "<" ++ x ++ ": " ++ pretty t ++ ">-> " ++ pretty e
>     LambdaSyntax _ _ x Nothing e -> "<" ++ x ++ ">-> " ++ pretty e
>     IdentSyntax _ s -> s
>     AppSyntax _ ManyMode f a -> "(" ++ pretty f ++ ")(" ++ pretty a ++ ")"
>     AppSyntax _ _ f a -> "(" ++ pretty f ++ ")<" ++ pretty a ++ ">"
>     ImmediateAppSyntax _ x params v e -> "let " ++ x ++ prettyParams params ++ " = " ++ pretty v ++ " in " ++ pretty e
>     NatSyntax _ n -> show n
>     NatTypeSyntax _ -> "Nat"
>     SortSyntax _ TypeSort -> "Type"
>     SortSyntax _ KindSort -> "Kind"
>     PiSyntax _ ManyMode x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")=> " ++ pretty e
>     PiSyntax _ _ x t e -> "<" ++ x ++ ": " ++ pretty t ++ ">=> " ++ pretty e
>     JSyntax _ a b c d e -> "J(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty c ++ ", " ++ pretty d ++ ", " ++ pretty e ++ ")"
>     IntersectionTypeSyntax _ x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")&" ++ pretty e
>     IntersectionSyntax p a b x xt r -> "[" ++ pretty a ++ ", " ++ pretty b ++ "; " ++ pretty (IntersectionTypeSyntax p x xt r) ++ "]"
>     FstSyntax _ a -> ".1(" ++ pretty a ++ ")"
>     SndSyntax _ a -> ".2(" ++ pretty a ++ ")"
>     EqSyntax _ a b t -> "(" ++ pretty a ++ ") =" ++ pretty t ++ "= (" ++ pretty b ++ ")"
>     ReflSyntax _ a t -> "refl(" ++ pretty a ++ ", " ++ pretty t ++ ")"
>     InterEqSyntax _ eq i j t -> "^(" ++ pretty eq ++ "; " ++ pretty i ++ ", " ++ pretty j ++ "; " ++ pretty t ++ ")"
>     CastSyntax _ a b eq -> "cast(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty eq ++ ", " ++ ")"
>     ExFalsoSyntax _ a -> "exfalso(" ++ pretty a ++ ")"

> data Term = Lambda Pos BinderMode String (Maybe Term) Term
>           | Ident Pos BinderMode Sort Int String
>           | App Pos BinderMode Term Term
>           | Nat Pos Int
>           | NatType Pos
>           | Sort Pos Sort
>           | Pi Pos BinderMode String Term Term
>           | J Pos Term Term Term Term Term
>           | IntersectionType Pos String Term Term
>           | Intersection Pos Term Term String Term Term
>           | Fst Pos Term
>           | Snd Pos Term
>           | Eq Pos Term Term Term
>           | Refl Pos Term Term
>           | InterEq Pos Term Term Term Term
>           | Cast Pos Term Term Term
>           | ExFalso Pos Term
>           deriving Show

> instance Pretty Term where
>   pretty t = case t of
>     Lambda _ ManyMode x (Just ty) e -> "(" ++ x ++ ": " ++ pretty ty ++ ")-> " ++ pretty e
>     Lambda _ ManyMode x Nothing e -> "(" ++ x ++ ")-> " ++ pretty e
>     Lambda _ _ x (Just ty) e -> "<" ++ x ++ ": " ++ pretty ty ++ ">-> " ++ pretty e
>     Lambda _ _ x Nothing e -> "<" ++ x ++ ">-> " ++ pretty e
>     Ident _ _ _ _ x -> x
>     App _ ManyMode foo bar -> "(" ++ pretty foo ++ ")(" ++ pretty bar ++ ")"
>     App _ _ foo bar -> "(" ++ pretty foo ++ ")<" ++ pretty bar ++ ">"
>     Nat _ n -> show n
>     NatType _ -> "Nat"
>     Sort _ TypeSort -> "Type"
>     Sort _ KindSort -> "Kind"
>     Pi _ ManyMode x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")=> " ++ pretty e
>     Pi _ _ x ty e -> "<" ++ x ++ ": " ++ pretty ty ++ ">=> " ++ pretty e
>     J _ a b c d e -> "J(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty c ++ ", " ++ pretty d ++ ", " ++ pretty e ++ ")"
>     IntersectionType _ x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")&" ++ pretty e
>     Intersection p a b x xt r -> "[" ++ pretty a ++ ", " ++ pretty b ++ "; " ++ pretty (IntersectionType p x xt r) ++ "]"
>     Fst _ a -> ".1(" ++ pretty a ++ ")"
>     Snd _ a -> ".2(" ++ pretty a ++ ")"
>     Eq _ a b ty -> "(" ++ pretty a ++ ") =" ++ pretty ty ++ "= (" ++ pretty b ++ ")"
>     Refl _ a ty -> "refl(" ++ pretty a ++ ", " ++ pretty ty ++ ")"
>     InterEq _ eq i j ty -> "^(" ++ pretty eq ++ "; " ++ pretty i ++ ", " ++ pretty j ++ "; " ++ pretty ty ++ ")"
>     Cast _ a b eq -> "cast(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty eq ++ ", " ++ ")"
>     ExFalso _ a -> "exfalso(" ++ pretty a ++ ")"

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
>   (ident, let_type, params, mb_t) <- do
>     mb_params <- possible parseParams
>     _ <- whitespace0
>     res <- possible $ char ':'
>     mb_t <- case res of
>       Just _ -> Just <$> parseTerm
>       Nothing -> return Nothing
>     case mb_params of
>       Just params -> do
>         _ <- char '='
>         return (i, Basic, params, mb_t)
>       Nothing -> do
>         op <- oneOf [exact "=", exact "<-"]
>         case op of
>           "=" -> return (i, Basic, [], mb_t)
>           "<-" -> return (i, Back, [], mb_t)
>           _ -> error "internal error"
>   val <- parseTerm
>   _ <- exact "in"
>   _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
>   scope <- parseTerm
>   return $ case let_type of
>     Basic -> ImmediateAppSyntax p ident params val scope
>     Back -> AppSyntax p ManyMode val (LambdaSyntax p ManyMode ident mb_t scope)

> buildPi :: Pos -> [(BinderMode, String, Syntax)] -> Syntax -> Syntax
> buildPi _p [] t = t
> buildPi p [(binder_mode, x, xt)] rett = PiSyntax p binder_mode x xt rett
> buildPi p ((binder_mode, x, xt):xs) rett = PiSyntax p binder_mode x xt (buildPi p xs rett)

> buildLambda :: Pos -> [(BinderMode, String, Maybe Syntax)] -> Syntax -> Syntax
> buildLambda _p [] e = e
> buildLambda p ((binder_mode, x, xt):xs) e = LambdaSyntax p binder_mode x xt (buildLambda p xs e)

> parseParens :: Parser Syntax
> parseParens = do
>   p <- position
>   _ <- char '('
>   _ <- whitespace0
>   res <- possible identString
>   case res of
>     Just x -> do
>       _ <- whitespace0
>       res2 <- possible $ char ':'
>       case res2 of
>         Just _ -> do
>           t <- parseTerm
>           _ <- char ')'
>           _ <- whitespace0
>           next <- oneOf [exact "&", exact "->", exact "=>"]
>           _ <- whitespace0
>           right <- parseTerm
>           case next of
>             "&" -> return $ IntersectionTypeSyntax p x t right
>             "->" -> return $ LambdaSyntax p ManyMode x (Just t) right
>             "=>" -> return $ PiSyntax p ManyMode x t right
>             _ -> error "internal error"
>         Nothing -> do
>           _ <- whitespace0
>           _ <- char ')'
>           _ <- whitespace0
>           res3 <- possible $ exact "->"
>           case res3 of
>             Just _ -> LambdaSyntax p ManyMode x Nothing <$> parseTerm
>             Nothing -> return $ IdentSyntax p x
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
>   _ <- char '<'
>   _ <- whitespace0
>   x <- patternString
>   _ <- whitespace0
>   res <- possible $ char ':'
>   t <- case res of
>     Just _ -> Just <$> parseTerm
>     Nothing -> return Nothing
>   _ <- char '>'
>   _ <- whitespace0
>   res2 <- oneOf [exact "->", exact "=>"]
>   right <- parseTerm
>   case res2 of
>     "->" -> return $ LambdaSyntax p ZeroMode x t right
>     "=>" -> return $ PiSyntax p ZeroMode x (fromJust t) right
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
>   (IntersectionTypeSyntax _ x xt rt) <- parseTerm
>   _ <- whitespace0
>   _ <- char ']'
>   return $ IntersectionSyntax p l r x xt rt

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

> parseTermNoPostfix :: Parser Syntax
> parseTermNoPostfix = do
>   _ <- whitespace0
>   t <- oneOf
>     [ parseParens
>     , parseErased
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
>     , parseIdent
>     ]
>   _ <- whitespace0
>   return t

> data Postfix = AppPostfix Pos Syntax
>              | ErasedAppPostfix Pos Syntax
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
>       _ <- char '<'
>       arg <- parseTerm
>       _ <- char '>'
>       return $ ErasedAppPostfix p2 arg
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

> parseParams :: Parser [(BinderMode, String, Maybe Syntax)]
> parseParams = many $ do
>     res <- oneOf [char '(', char '<']
>     _ <- whitespace0
>     param <- patternString
>     _ <- whitespace0
>     res2 <- possible $ char ':'
>     case (res, res2) of
>       ('(', Just _) -> do
>         t <- parseTerm
>         _ <- char ')'
>         return (ManyMode, param, Just t)
>       ('<', Just _) -> do
>         t <- parseTerm
>         _ <- char '>'
>         return (ZeroMode, param, Just t)
>       ('(', Nothing) -> do
>         _ <- char ')'
>         return (ManyMode, param, Nothing)
>       ('<', Nothing) -> do
>         _ <- char '>'
>         return (ZeroMode, param, Nothing)
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
> sortOf renames (Pi _ _ _ _ body) = sortOf renames body
> sortOf _renames (NatType _) = TypeSort
> sortOf _renames (Sort _ _) = KindSort
> sortOf _renames _term = error "internal error"

> translate :: Int -> Map.Map String (Int, BinderMode, Sort) -> [Term] -> Syntax -> Either String Term
> translate index renames psi t =
>   let tr = translate in
>   case t of
>     LambdaSyntax p binder_mode param mb_ty body ->
>       case mb_ty of
>         Just ty -> do
>           ty2 <- tr index renames [] ty
>           body2 <- tr (index + 1) (Map.insert param (index, binder_mode, sortOf renames ty2) renames) (tail psi) body
>           return $ Lambda p binder_mode param (Just ty2) body2
>         Nothing -> 
>           case psi of
>             arg:rest -> do
>               body2 <- tr (index + 1) (Map.insert param (index, binder_mode, sortOf renames arg) renames) rest body
>               return $ Lambda p binder_mode param Nothing body2
>             [] -> Left $ "Type error. This lambda needs a type annotation (" ++ show p ++ ")"
>     IdentSyntax p ('#':name) -> return $ Ident p ManyMode TypeSort 0 $ '#':name
>     IdentSyntax p name ->
>       case Map.lookup name renames of
>         Just (i, bm, sort) -> return $ Ident p bm sort (index - i - 1) name
>         Nothing -> Left $ prettyParseError p Nothing $ "undefined variable `" ++ name ++ "`"
>     AppSyntax p bm foo bar -> do
>       bar2 <- tr index renames [] bar
>       foo2 <- tr index renames (bar2:psi) foo
>       return $ App p bm foo2 bar2
>     ImmediateAppSyntax p x params v e -> do
>       v2 <- tr index renames [] (buildLambda p params v)
>       let binder_mode = getBinderMode v2
>       e2 <- tr (index + 1) (Map.insert x (index, binder_mode, sortOf renames v2) renames) psi e
>       return $ App p binder_mode (Lambda p binder_mode x Nothing e2) v2
>     NatSyntax p n -> return $ Nat p n
>     NatTypeSyntax p -> return $ NatType p
>     SortSyntax p s -> return $ Sort p s
>     PiSyntax p binder_mode param ty body -> do
>       ty2 <- tr index renames [] ty
>       body2 <- tr (index + 1) (Map.insert param (index, binder_mode, sortOf renames ty2) renames) psi body
>       return $ Pi p binder_mode param ty2 body2
>     JSyntax p eq a b c predicate -> do
>       eq2 <- tr index renames [] eq
>       a2 <- tr index renames [] a
>       b2 <- tr index renames [] b
>       c2 <- tr index renames [] c
>       predicate2 <- tr index renames [] predicate
>       return $ J p eq2 a2 b2 c2 predicate2
>     EqSyntax p a b ty -> do
>       a2 <- tr index renames [] a
>       b2 <- tr index renames [] b
>       ty2 <- tr index renames [] ty
>       return $ Eq p a2 b2 ty2
>     ReflSyntax p x ty -> do
>       x2 <- tr index renames [] x
>       ty2 <- tr index renames [] ty
>       return $ Refl p x2 ty2
>     IntersectionTypeSyntax p x xt r -> do
>       xt2 <- tr index renames [] xt
>       r2 <- tr index (Map.insert x (index, ZeroMode, TypeSort) renames) [] r
>       return $ IntersectionType p x xt2 r2
>     IntersectionSyntax p a b x xt r -> do
>       a2 <- tr index renames psi a
>       b2 <- tr index (Map.insert x (index, ZeroMode, TypeSort) renames) psi b
>       xt2 <- tr index renames [] xt
>       r2 <- tr index (Map.insert x (index, ZeroMode, TypeSort) renames) [] r
>       return $ Intersection p a2 b2 x xt2 r2
>     FstSyntax p a -> do
>       a2 <- tr index renames psi a
>       return $ Fst p a2
>     SndSyntax p a -> do
>       a2 <- tr index renames psi a
>       return $ Snd p a2
>     _ -> undefined

> shift :: Int -> Term -> Term
> shift n term = case term of
>   Ident p bm s i str | i >= n -> Ident p bm s (i + 1) str
>   Pi p mode x xt body -> Pi p mode x (shift n xt) (shift (n+1) body)
>   Lambda p mode x xt body -> Lambda p mode x (shift n <$> xt) (shift (n+1) body)
>   IntersectionType p x xt body -> IntersectionType p x (shift n xt) (shift (n+1) body)
>   App p mode foo bar -> App p mode (shift n foo) (shift n bar)
>   J p a b c d e -> J p (shift n a) (shift n b) (shift n c) (shift n d) (shift n e)
>   Intersection p a b x xt r -> Intersection p (shift n a) (shift (n+1) b) x (shift n xt) (shift (n+1) r)
>   Fst p a -> Fst p (shift n a)
>   Snd p a -> Snd p (shift n a)
>   Eq p a b t -> Eq p (shift n a) (shift n b) (shift n t)
>   Refl p a t -> Refl p (shift n a) (shift n t)
>   InterEq p eq a b t -> InterEq p (shift n eq) (shift n a) (shift n b) (shift n t)
>   Cast p a b t -> Cast p (shift n a) (shift n b) (shift n t)
>   ExFalso p a -> ExFalso p (shift n a)
>   _ -> term

> subst :: Term -> Int -> Term -> Term
> subst term depth new = case term of
>   Ident _ _ _ i _ -> if depth == i then new else term
>   Pi p mode x xt body -> Pi p mode x (subst xt depth new) (subst body (depth + 1) (shift 0 new))
>   Lambda p mode x xt body -> Lambda p mode x xt (subst body (depth + 1) (shift 0 new))
>   IntersectionType p x xt body -> IntersectionType p x xt (subst body (depth + 1) (shift 0 new))
>   App p mode foo bar -> App p mode (subst foo depth new) (subst bar depth new)
>   J p a b c d e -> J p (subst a depth new) (subst b depth new) (subst c depth new) (subst d depth new) (subst e depth new)
>   Intersection p a b x xt r -> Intersection p (subst a depth new) (subst b (depth + 1) (shift 0 new)) x (subst xt depth new) (subst r (depth + 1) (shift 0 new))
>   Fst p a -> Fst p (subst a depth new)
>   Snd p a -> Snd p (subst a depth new)
>   Eq p a b t -> Eq p (subst a depth new) (subst b depth new) (subst t depth new)
>   Refl p a t -> Refl p (subst a depth new) (subst t depth new)
>   InterEq p eq a b t -> InterEq p (subst eq depth new) (subst a depth new) (subst b depth new) (subst t depth new)
>   Cast p a b t -> Cast p (subst a depth new) (subst b depth new) (subst t depth new)
>   ExFalso p a -> ExFalso p (subst a depth new)
>   _ -> term

> identity :: Pos -> Term
> identity p = Lambda p ManyMode "x" Nothing $ Ident p ManyMode TypeSort 0 "x"

> termEq :: [(BinderMode, Term, Maybe Term)] -> Term -> Term -> Bool
> termEq gamma a b = case (eval gamma a, eval gamma b) of
>   (Ident _ _ _ i _, Ident _ _ _ j _) -> i == j
>   (NatType _, NatType _) -> True
>   (Sort _ s1, Sort _ s2) -> s1 == s2
>   (Pi _ mode1 _ xt body1, Pi _ mode2 _ yt body2) -> mode1 == mode2 && termEq gamma xt yt && termEq ((mode1,xt,Nothing):gamma) body1 body2
>   (Lambda _ mode1 _ _xt body1, Lambda _ mode2 _ _yt body2) -> mode1 == mode2 && termEq ((mode1,body1,Nothing):gamma) body1 body2 -- using body1 as a dummy type because it won't matter
>   (App _ _ foo1 bar1, App _ _ foo2 bar2) -> termEq gamma foo1 foo2 && termEq gamma bar1 bar2
>   (Nat _ n, Nat _ m) -> n == m
>   (J p _ _ _ _ _, t) -> termEq gamma t $ identity p
>   (t, J p _ _ _ _ _) -> termEq gamma t $ identity p
>   (Refl p _ _, t) -> termEq gamma t $ identity p
>   (t, Refl p _ _) -> termEq gamma t $ identity p
>   (Eq _ l1 r1 t1, Eq _ l2 r2 t2) -> termEq gamma l1 l2 && termEq gamma r1 r2 && termEq gamma t1 t2
>   (IntersectionType _ _ xt t1, IntersectionType _ _ yt t2) -> termEq gamma xt yt && termEq ((ZeroMode,xt,Nothing):gamma) t1 t2
>   (Intersection _ l1 _ _ _ _, Intersection _ l2 _ _ _ _) -> termEq gamma l1 l2
>   (Fst _ i, Fst _ j) -> termEq gamma i j
>   (Snd _ i, Snd _ j) -> termEq gamma i j
>   _ -> False

> idx :: [a] -> Int -> Maybe a
> idx xs i = case xs of
>   [] -> Nothing
>   (x:rest) -> if i == 0 then Just x else idx rest (i - 1)

> eval :: [(BinderMode, Term, Maybe Term)] -> Term -> Term
> eval gamma term = case term of
>   Ident _ _ _ i _ -> case gamma `idx` i of
>     Just (_, _, Just v) -> eval gamma v
>     _ -> term
>   App _ _ foo bar -> case eval gamma foo of
>     Lambda p mode _ _ body -> eval ((mode, NatType p, Just bar):gamma) body -- NatType p as a dummy type, since eval doesn't depend on types
>     _ -> term
>   Fst _ (Intersection _ l _ _ _ _) -> l
>   Snd _ (Intersection _ _ r _ _ _) -> r
>   _ -> term

> getBinderMode :: Term -> BinderMode
> getBinderMode ty = case ty of
>   Pi _ _ _ _ body -> getBinderMode body -- this matters when we distinguish between ZeroMode and TypeMode; for now it's always ZeroMode
>   Lambda _ _ _ _ body -> getBinderMode body
>   Ident _p bm _ _i _n -> bm
>   App _ _ foo _ -> getBinderMode foo
>   Nat _ _ -> ManyMode
>   NatType _ -> ZeroMode
>   Sort _ _ -> ZeroMode
>   Eq {} -> ZeroMode
>   Refl {} -> ManyMode
>   J {} -> ManyMode
>   IntersectionType {} -> ZeroMode
>   Intersection _ _ l _ _ _ -> getBinderMode l
>   Fst _ i -> getBinderMode i
>   Snd _ i -> getBinderMode i
>   t -> error $ "getBinderMode: " ++ show t

> infer :: Maybe Term -> [(BinderMode, Term, Maybe Term)] -> [Term] -> Term -> Either String Term
> infer arg gamma psi term = case term of
>   Lambda p mode x mb_xt body -> do
>     let xt = fromMaybe (head psi) mb_xt
>     _ <- infer Nothing gamma [] xt
>     let gamma2 = (mode, shift 0 xt, arg):gamma
>     body_t <- infer Nothing gamma2 (tail psi) body
>     return $ Pi p mode x xt body_t
>   App _ mode foo bar -> do
>     bar_t <- infer Nothing gamma [] bar
>     foo_t <- infer (Just bar) gamma (bar_t:psi) foo
>     case foo_t of
>       Pi _ mode2 _ xt body_t ->
>         if mode == mode2 then do
>           if termEq gamma xt bar_t then
>               return $ subst body_t 0 bar
>           else Left $ "type mismatch, expected " ++ pretty xt ++ ", got " ++ pretty bar_t
>         else Left $ "mode mismatch, expected " ++ show mode2 ++ ", got " ++ show mode
>       _ -> Left $ "expected function, got " ++ pretty foo_t
>   Pi p mode _ xt body -> do
>     _ <- infer Nothing gamma [] xt
>     _ <- infer arg ((mode, xt, arg):map (\(a,b,c)->(a,shift 0 b,c)) gamma) [] body
>     return $ Sort p TypeSort -- TODO: should be sortOf body_t
>   NatType p -> return $ Sort p TypeSort
>   Sort p _ -> return $ Sort p KindSort
>   Nat p _ -> return $ NatType p
>   Ident _ _ _ i _ -> let (_, t, _) = gamma !! i in return t
>   J p eq a b c predicate -> do
>     eq_t <- infer Nothing gamma [] eq
>     a_t <- infer Nothing gamma [] a
>     b_t <- infer Nothing gamma [] b
>     if termEq gamma a_t b_t then
>       case eq_t of
>         Eq _ l r t | termEq gamma a l && termEq gamma b r && termEq gamma a_t t -> do
>           if termEq gamma c t then do
>             pred_t <- infer Nothing gamma [] predicate
>             case pred_t of
>               Pi _ ZeroMode var_name param_t (Pi _ ZeroMode _var2_name (Eq _ l2 r2 t2) (Sort _ TypeSort)) | termEq gamma param_t t && termEq gamma a l2 && termEq gamma (Ident p ZeroMode TypeSort 0 var_name) r2 && termEq gamma t t2-> do
>                 return $ Pi p ManyMode "_" (App p ZeroMode (App p ZeroMode predicate a) (Refl p a t)) (App p ZeroMode (App p ZeroMode predicate b) eq)
>               _ -> Left $ "type error, the predicate of J has an invalid type (`" ++ pretty pred_t ++ "`)"   
>           else Left $ "type error, the fourth argument of J must be the type of the first two arguments (`" ++ pretty t ++ "` != `" ++ pretty c ++ "`)"
>         _ -> Left $ "type error, the first three arguments of J don't form a valid equation (`" ++ pretty eq_t ++ "`, `" ++ pretty a_t ++ "`, `" ++ pretty b_t ++ "`)"
>     else Left $ "type mismatch, J equatees must have the same type (`" ++ pretty a_t ++ "` and `" ++ pretty b_t ++ "` are not equal)"
>   Eq p l r t -> do
>     l_t <- infer Nothing gamma [] l
>     r_t <- infer Nothing gamma [] r
>     if termEq gamma l_t r_t && termEq gamma l_t t then
>       return $ Sort p TypeSort
>     else Left $ "type mismatch, Eq equatees must have the same type (`" ++ pretty l_t ++ "` and `" ++ pretty r_t ++ "` should convert to `" ++ pretty t ++ "`)"
>   Refl p a t -> do
>     a_t <- infer Nothing gamma [] a
>     if termEq gamma a_t t then
>       return $ Eq p a a t
>     else Left $ "type mismatch, Refl first argument must have second argument as type (`" ++ pretty a_t ++ "` != `" ++ pretty t ++ "`)"
>   IntersectionType p _x a b -> do
>     _ <- infer Nothing gamma [] a
>     _ <- infer Nothing ((ZeroMode,a,Nothing):gamma) [] b
>     return $ Sort p TypeSort
>   Intersection p l r x l_t_2 r_t_2 -> 
>     if termEq gamma l r then do
>       l_t <- infer Nothing gamma [] l
>       r_t <- infer Nothing ((ZeroMode,l_t,Just l):gamma) [] r
>       _ <- infer Nothing gamma [] $ IntersectionType p x l_t_2 r_t_2
>       if termEq gamma l_t l_t_2 && termEq ((ZeroMode,l_t,Just l):gamma) r_t r_t_2 then
>         return $ IntersectionType p x l_t_2 r_t_2
>       else Left $ "type mismatch, Intersection equatees don't match type annotation (`&" ++ x ++ ": " ++ pretty l_t ++ ". " ++ pretty r_t ++ "` should convert to `&" ++ x ++ ": " ++ pretty l_t_2 ++ ". " ++ pretty r_t_2 ++ "`)"
>     else Left $ "type mismatch, Intersection equatees aren't definitionally equal (`" ++ pretty l ++ "` != `" ++ pretty r ++ "`)"
>   Fst _ i -> do
>     i_t <- infer Nothing gamma [] i
>     case i_t of
>       IntersectionType _ _ l _ -> return l
>       _ -> Left $ "type error, Fst argument must be an intersection, but instead has type `" ++ pretty i_t ++ "`"
>   Snd _ i -> do
>     i_t <- infer Nothing gamma [] i
>     case i_t of
>       IntersectionType _ _ _ r -> return $ subst r 0 i
>       _ -> Left $ "type error, Snd argument must be an intersection, but instead has type `" ++ pretty i_t ++ "`"
>   _ -> undefined

> captures :: [Int] -> Int -> Term -> Set.Set Int
> captures caps depth t = case t of
>   Lambda _ _ _ _ body -> Set.map (\n->n-1) $ captures caps (depth + 1) body
>   Ident _ _ _ i _ ->
>     if i < depth then Set.empty else Set.singleton i
>   App _ ManyMode foo bar -> captures caps depth foo `Set.union` captures caps depth bar
>   App _ ZeroMode foo _bar -> captures caps depth foo
>   Intersection _ l _ _ _ _ -> captures caps depth l
>   Fst _ i -> captures caps depth i
>   Snd _ i -> captures caps depth i
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
>   Lambda _ ManyMode _ _ body -> 
>     let body_caps = Set.toAscList $ captures [] 1 body in
>     let body_cap_indices = map (\n->fromMaybe (-1) (elemIndex (n-1) caps) + 1) body_caps in
>     let body_ops = codegen body_caps kcaps body in
>     concatMap capOp (reverse body_cap_indices) ++ lamOp (length body_ops + 1) ++ body_ops ++ retOp
>   Lambda _ ZeroMode _ _ body -> codegen caps kcaps body
>   Ident _ _ _ i _ ->
>     case elemIndex i caps of
>       Just index -> varOp (index + 1)
>       Nothing -> varOp 0
>   App _ ManyMode foo bar -> 
>     let bar_caps = Set.toAscList $ captures [] 0 bar in
>     codegen caps bar_caps foo ++ codegen caps kcaps bar ++ concatMap capOp kcaps ++ appOp
>   App _ ZeroMode foo _bar -> codegen caps kcaps foo
>   Nat _ n -> litOp n
>   J {} -> lamOp 3 ++ varOp 0 ++ retOp -- J compiles to the unerased identity function
>   Refl {} -> lamOp 3 ++ varOp 0 ++ retOp -- Refl compiles to the unerased identity function
>   Intersection  _ l _ _ _ _ -> codegen caps kcaps l
>   Fst _ i -> codegen caps kcaps i
>   Snd _ i -> codegen caps kcaps i
>   _ -> undefined