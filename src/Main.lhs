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
> import Data.Bifunctor (second)
  
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
>             case infer [] t2 of
>               Left err -> putStrLn err
>               Right _t3 -> do
>                 let bytecode = codegen [] t2 ++ [29, 0]
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

> data BinderMode = ZeroMode | ManyMode | TypeMode deriving (Show, Eq)

> data Sort = TypeSort | KindSort deriving (Show, Eq)

> data Syntax = LambdaSyntax Pos BinderMode String Syntax Syntax
>             | IdentSyntax Pos String
>             | AppSyntax Pos BinderMode Syntax Syntax
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
>             | InterEqSyntax Pos Syntax Syntax Syntax Syntax
>             | CastSyntax Pos Syntax Syntax Syntax
>             | ExFalsoSyntax Pos Syntax
>             deriving Show

> stxPos :: Syntax -> Pos
> stxPos stx = case stx of
>   LambdaSyntax p _ _ _ _ -> p
>   IdentSyntax p _ -> p
>   AppSyntax p _ _ _ -> p
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
>   InterEqSyntax p _ _ _ _ -> p
>   CastSyntax p _ _ _ -> p
>   ExFalsoSyntax p _ -> p

> instance Pretty Syntax where
>   pretty stx = case stx of
>     LambdaSyntax _ ManyMode x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")-> " ++ pretty e
>     LambdaSyntax _ _ x t e -> "<" ++ x ++ ": " ++ pretty t ++ ">-> " ++ pretty e
>     IdentSyntax _ s -> s
>     AppSyntax _ ManyMode f a -> "(" ++ pretty f ++ ")(" ++ pretty a ++ ")"
>     AppSyntax _ _ f a -> "(" ++ pretty f ++ ")<" ++ pretty a ++ ">"
>     NatSyntax _ n -> show n
>     NatTypeSyntax _ -> "Nat"
>     SortSyntax _ TypeSort -> "Type"
>     SortSyntax _ KindSort -> "Kind"
>     PiSyntax _ ManyMode x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")=> " ++ pretty e
>     PiSyntax _ _ x t e -> "<" ++ x ++ ": " ++ pretty t ++ ">=> " ++ pretty e
>     JSyntax _ a b c d e -> "J(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty c ++ ", " ++ pretty d ++ ", " ++ pretty e ++ ")"
>     IntersectionTypeSyntax _ x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")&" ++ pretty e
>     IntersectionSyntax _ a b t -> "[" ++ pretty a ++ ", " ++ pretty b ++ "; " ++ pretty t ++ "]"
>     FstSyntax _ a -> ".1(" ++ pretty a ++ ")"
>     SndSyntax _ a -> ".2(" ++ pretty a ++ ")"
>     EqSyntax _ a b t -> "(" ++ pretty a ++ ") =" ++ pretty t ++ "= (" ++ pretty b ++ ")"
>     ReflSyntax _ a t -> "refl(" ++ pretty a ++ ", " ++ pretty t ++ ")"
>     InterEqSyntax _ eq i j t -> "^(" ++ pretty eq ++ "; " ++ pretty i ++ ", " ++ pretty j ++ "; " ++ pretty t ++ ")"
>     CastSyntax _ a b eq -> "cast(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty eq ++ ", " ++ ")"
>     ExFalsoSyntax _ a -> "exfalso(" ++ pretty a ++ ")"

> data Term = Lambda Pos BinderMode String Term Term
>           | Ident Pos Sort Int String
>           | App Pos BinderMode Term Term
>           | Nat Pos Int
>           | NatType Pos
>           | Sort Pos Sort
>           | Pi Pos BinderMode String Term Term
>           | J Pos Term Term Term Term Term
>           | IntersectionType Pos String Term Term
>           | Intersection Pos Term Term Term
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
>     Lambda _ ManyMode x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")-> " ++ pretty e
>     Lambda _ _ x ty e -> "<" ++ x ++ ": " ++ pretty ty ++ ">-> " ++ pretty e
>     Ident _ _ _ x -> x
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
>     Intersection _ a b ty -> "[" ++ pretty a ++ ", " ++ pretty b ++ "; " ++ pretty ty ++ "]"
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
>         return (i, Basic, params, t)
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
>   let val2 = buildLambda p params t val
>   return $ case let_type of
>     Basic -> AppSyntax p ManyMode (LambdaSyntax p ManyMode ident (buildPi p params t) scope) val2
>     Back -> AppSyntax p ManyMode val (LambdaSyntax p ManyMode ident t scope)

> buildPi :: Pos -> [(BinderMode, String, Syntax)] -> Syntax -> Syntax
> buildPi _p [] t = t
> buildPi p [(binder_mode, x, xt)] rett = PiSyntax p binder_mode x xt rett
> buildPi p ((binder_mode, x, xt):xs) rett = PiSyntax p binder_mode x xt (buildPi p xs rett)

> buildLambda :: Pos -> [(BinderMode, String, Syntax)] -> Syntax -> Syntax -> Syntax
> buildLambda _p [] _t e = e
> buildLambda p ((binder_mode, x, xt):xs) rett e = LambdaSyntax p binder_mode x xt (buildLambda p xs rett e)

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
>             "->" -> return $ LambdaSyntax p ManyMode x t right
>             "=>" -> return $ PiSyntax p ManyMode x t right
>             _ -> error "internal error"
>         Nothing -> do
>           _ <- whitespace0
>           _ <- char ')'
>           return $ IdentSyntax p x
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
>   _ <- char ':'
>   t <- parseTerm
>   _ <- char '>'
>   _ <- whitespace0
>   res <- oneOf [exact "->", exact "=>"]
>   right <- parseTerm
>   case res of
>     "->" -> return $ LambdaSyntax p ZeroMode x t right
>     "=>" -> return $ PiSyntax p ZeroMode x t right
>     _ -> error "internal error"

> parseTermNoPostfix :: Parser Syntax
> parseTermNoPostfix = do
>   _ <- whitespace0
>   t <- oneOf
>     [ parseParens
>     , parseErased
>     , parseNat
>     , parseLet
>     , parseNatType
>     , parseTypeSort
>     , parseKindSort
>     , parseIdent
>     ]
>   _ <- whitespace0
>   return t

> data Postfix = AppPostfix Pos Syntax
>              | ErasedAppPostfix Pos Syntax
> --           | MonoidPostfix Pos [Syntax]
>              | ApostrophePrefix Pos Syntax

> parseTerm :: Parser Syntax
> parseTerm = do
>   t <- parseTermNoPostfix
>   args <- many0 $ oneOf
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
>       ApostrophePrefix p2 <$> parseTerm
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
>             ApostrophePrefix p2 rhs -> AppSyntax p2 ManyMode b rhs
>           ) t args
>   _ <- whitespace0
>   return out

> parseParams :: Parser [(BinderMode, String, Syntax)]
> parseParams = many $ do
>     res <- oneOf [char '(', char '<']
>     _ <- whitespace0
>     param <- patternString
>     _ <- whitespace0
>     _ <- char ':'
>     t <- parseTerm
>     case res of
>       '(' -> do
>         _ <- char ')'
>         return (ManyMode, param, t)
>       '<' -> do
>         _ <- char '>'
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
>       let body2 = buildLambda p params t body
>       return $ Left (name, (t, body2))

> parseFile :: Parser (Map.Map String (Syntax, Syntax), [[String]])
> parseFile = do
>   let parser = many $ whitespace0 *>
>         parseDecl <* whitespace0
>   (decls, imports) <- fmap partitionEithers parser
>   return (Map.fromList decls, imports)

> sortOf :: Map.Map String (Int, Sort) -> Syntax -> Sort
> sortOf renames (IdentSyntax _ s) = case Map.lookup s renames of
>   Just (_, sort) -> sort
>   Nothing -> error "internal error"
> sortOf renames (PiSyntax _ _ _ _ body) = sortOf renames body
> sortOf _renames (NatTypeSyntax _) = TypeSort
> sortOf _renames (SortSyntax _ _) = KindSort
> sortOf _renames _term = error "internal error"

> translate :: Int -> Map.Map String (Int, Sort) -> Syntax -> Either String Term
> translate index renames t =
>   let tr = translate in
>   case t of
>     LambdaSyntax p binder_mode param ty body -> do
>       ty2 <- tr index renames ty
>       body2 <- tr (index + 1) (Map.insert param (index, sortOf renames ty) renames) body
>       return $ Lambda p binder_mode param ty2 body2
>     IdentSyntax p ('#':name) -> return $ Ident p TypeSort 0 $ '#':name
>     IdentSyntax p name ->
>       case Map.lookup name renames of
>         Just (i, sort) -> return $ Ident p sort (index - i - 1) name
>         Nothing -> Left $ prettyParseError p Nothing $ "undefined variable `" ++ name ++ "`"
>     AppSyntax p binder_mode foo bar -> do
>       foo2 <- tr index renames foo
>       bar2 <- tr index renames bar
>       return $ App p binder_mode foo2 bar2
>     NatSyntax p n -> return $ Nat p n
>     NatTypeSyntax p -> return $ NatType p
>     SortSyntax p s -> return $ Sort p s
>     PiSyntax p binder_mode param ty body -> do
>       ty2 <- tr index renames ty
>       body2 <- tr (index + 1) (Map.insert param (index, sortOf renames ty) renames) body
>       return $ Pi p binder_mode param ty2 body2
>     _ -> undefined

> shift :: Int -> Term -> Term
> shift n term = case term of
>   Ident p s i str | i >= n -> Ident p s (i + 1) str
>   Pi p mode x xt body -> Pi p mode x (shift n xt) (shift (n+1) body)
>   Lambda p mode x xt body -> Lambda p mode x (shift n xt) (shift (n+1) body)
>   IntersectionType p x xt body -> IntersectionType p x (shift n xt) (shift (n+1) body)
>   App p mode foo bar -> App p mode (shift n foo) (shift n bar)
>   J p a b c d e -> J p (shift n a) (shift n b) (shift n c) (shift n d) (shift n e)
>   Intersection p a b t -> Intersection p (shift n a) (shift n b) (shift n t)
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
>   Ident _ _ i _ -> if depth == i then new else term
>   Pi p mode x xt body -> Pi p mode x (subst xt depth new) (subst body (depth + 1) (shift 0 new))
>   Lambda p mode x xt body -> Lambda p mode x xt (subst body (depth + 1) (shift 0 new))
>   IntersectionType p x xt body -> IntersectionType p x xt (subst body (depth + 1) (shift 0 new))
>   App p mode foo bar -> App p mode (subst foo depth new) (subst bar depth new)
>   J p a b c d e -> J p (subst a depth new) (subst b depth new) (subst c depth new) (subst d depth new) (subst e depth new)
>   Intersection p a b t -> Intersection p (subst a depth new) (subst b depth new) (subst t depth new)
>   Fst p a -> Fst p (subst a depth new)
>   Snd p a -> Snd p (subst a depth new)
>   Eq p a b t -> Eq p (subst a depth new) (subst b depth new) (subst t depth new)
>   Refl p a t -> Refl p (subst a depth new) (subst t depth new)
>   InterEq p eq a b t -> InterEq p (subst eq depth new) (subst a depth new) (subst b depth new) (subst t depth new)
>   Cast p a b t -> Cast p (subst a depth new) (subst b depth new) (subst t depth new)
>   ExFalso p a -> ExFalso p (subst a depth new)
>   _ -> term

> typeEq :: Term -> Term -> Bool
> typeEq a b = case (a, b) of
>   (Ident _ _ i _, Ident _ _ j _) -> i == j
>   (NatType _, NatType _) -> True
>   (Sort _ s1, Sort _ s2) -> s1 == s2
>   (Pi _ mode1 _ xt body1, Pi _ mode2 _ yt body2) -> mode1 == mode2 && typeEq xt yt && typeEq body1 body2
>   _ -> False

> infer :: [(BinderMode, Term)] -> Term -> Either String Term
> infer gamma term = case term of
>   Lambda p mode x xt body -> do
>     _ <- infer gamma xt
>     let gamma2 = (mode, shift 0 xt):gamma
>     body_t <- infer gamma2 body
>     return $ Pi p mode x xt body_t
>   App _ mode foo bar -> do
>     foo_t <- infer gamma foo
>     case foo_t of
>       Pi _ mode2 _ xt body_t ->
>         if mode == mode2 then do
>           bar_t <- infer gamma bar
>           if typeEq xt bar_t then
>               return $ subst body_t 0 bar
>           else Left $ "type mismatch, expected " ++ pretty xt ++ ", got " ++ pretty bar_t
>         else Left $ "mode mismatch, expected " ++ show mode2 ++ ", got " ++ show mode
>       _ -> Left $ "expected function, got " ++ pretty foo_t
>   Pi p mode _ xt body -> do
>     _ <- infer gamma xt
>     _ <- infer ((mode, xt):map (second $ shift 0) gamma) body
>     return $ Sort p TypeSort -- TODO: should be sortOf body_t
>   NatType p -> return $ Sort p TypeSort
>   Sort p _ -> return $ Sort p KindSort
>   Nat p _ -> return $ NatType p
>   Ident _ _ i _ -> let (_, t) = gamma !! i in return t
>   _ -> undefined

> captures :: [Int] -> Int -> Term -> Set.Set Int
> captures caps depth t = case t of
>   Lambda _ ManyMode _ _ body -> Set.map (\n->n-1) $ captures caps (depth + 1) body
>   Ident _ _ i _ ->
>     if i < depth then Set.empty else Set.singleton i
>   App _ ManyMode foo bar -> captures caps depth foo `Set.union` captures caps depth bar
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

> codegen :: [Int] -> Term -> [Word8]
> codegen caps t = case t of
>   Lambda _ ManyMode _ _ body -> 
>     let body_caps = Set.toAscList $ captures [] 1 body in
>     let body_cap_indices = map (\n->fromMaybe (-1) (elemIndex (n-1) caps) + 1) body_caps in
>     let body_ops = codegen body_caps body in
>     concatMap capOp (reverse body_cap_indices) ++ lamOp (length body_ops + 1) ++ body_ops ++ retOp
>   Lambda _ ZeroMode _ _ body -> codegen caps body
>   Ident _ _ i _ -> 
>     case elemIndex i caps of
>       Just idx -> varOp (idx + 1)
>       Nothing -> varOp 0
>   App _ ManyMode foo bar -> codegen caps foo ++ codegen caps bar ++ appOp
>   App _ ZeroMode foo _bar -> codegen caps foo
>   Nat _ n -> litOp n
>   _ -> undefined