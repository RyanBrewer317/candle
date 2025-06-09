module Parser where

import Header (Pos(..), Syntax(..), BinderMode(..), Sort(..))
import qualified Data.Map as Map
import Data.Either (partitionEithers)
import Data.Char (isAlpha, isDigit)
import Data.Functor (($>))
import Data.Maybe (fromMaybe)

newtype Parser a = Parser {
  run :: Maybe String -> Pos -> String -> Either String (a, Pos, String)
}

prettyParseError :: Pos -> Maybe String -> String -> String
prettyParseError (Pos srcName line col) expected msg =
  "Parse error. "
  ++ msg ++ " in `" ++ srcName ++ "` at "
  ++ show line ++ ":" ++ show col ++ "."
  ++ case expected of
    Just s -> " Expected " ++ s ++ "."
    Nothing -> ""

position :: Parser Pos
position = Parser $ \_ pos src -> Right (pos, pos, src)

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = Parser $ \expected (Pos srcName line col) src ->
  case src of
    c:rest | c == '\n' && p c -> Right (c, Pos srcName (line + 1) 0, rest)
    c:rest | p c -> Right (c, Pos srcName line (col + 1), rest)
    c:_ -> Left $
      prettyParseError (Pos srcName line col) expected $ "Unexpected `" ++ c:"`"
    [] -> Left $
      prettyParseError (Pos srcName line col) expected "Unexpected end of input"

instance Functor Parser where
  fmap f p = Parser $ \expected pos s -> case run p expected pos s of
    Left err -> Left err
    Right (x, pos2, rest) -> Right (f x, pos2, rest)

instance Applicative Parser where
  pure x = Parser $ \_ pos s -> Right (x, pos, s)
  pf <*> pa = Parser $ \expected pos s -> do -- Either monad, not Parser monad
    (f, pos2, rest) <- run pf expected pos s
    (a, pos3, rest2) <- run pa expected pos2 rest
    Right (f a, pos3, rest2)

instance Monad Parser where
  return = pure
  pa >>= f = Parser $ \expected pos s -> do
    (a, pos2, rest) <- run pa expected pos s
    run (f a) expected pos2 rest

instance MonadFail Parser where
  fail e = Parser $ \expected pos _s -> Left $ prettyParseError pos expected e

char :: Char -> Parser Char
char c = satisfy (==c)

oneOf :: [Parser a] -> Parser a
oneOf [p] = p
oneOf (p:ps) = Parser $ \expected pos s -> case run p expected pos s of
  Left _err -> run (oneOf ps) expected pos s
  Right (x, pos2, rest) -> Right (x, pos2, rest)
oneOf [] = error "oneOf on empty list of parsers"

possible :: Parser a -> Parser (Maybe a)
possible p = oneOf [fmap Just p, return Nothing]

many0 :: Parser a -> Parser [a]
many0 p = Parser $ \expected pos s -> case run p expected pos s of
  Left _ -> Right ([], pos, s)
  Right (x, pos2, rest) -> run ((x:) <$> many0 p) expected pos2 rest

many :: Parser a -> Parser [a]
many p = Parser $ \expected pos s -> do -- Either monad, not Parser monad
  (x, pos2, rest) <- run p expected pos s
  run ((x:) <$> many0 p) expected pos2 rest

exact :: String -> Parser String
exact s = foldr (\c p-> char c *> p) (return ()) s $> s

sepBy :: Parser a -> Parser b -> Parser [b]
sepBy by p = do
  b <- p
  bs <- many0 (by >> p)
  return (b:bs)

sepBy0 :: Parser a -> Parser b -> Parser [b]
sepBy0 by p = oneOf [sepBy by p, return []]

comment :: Parser Char
comment = do
  _ <- exact "//"
  _ <- many0 $ satisfy (/='\n')
  _ <- possible $ char '\n'
  return '\n'

whitespace0 :: Parser [Char]
whitespace0 = many0 $ oneOf [char ' ', char '\n', comment]

whitespace :: Parser [Char]
whitespace = many $ oneOf [char ' ', char '\n', comment]

identString :: Parser String
identString = do
  first <- satisfy isAlpha
  rest <- many0 $ oneOf [satisfy isAlpha, char '_', satisfy isDigit]
  return (first:rest)

patternString :: Parser String
patternString = oneOf
  [ identString
  , do
    _ <- char '_'
    mb_rest <- possible identString
    case mb_rest of
      Just rest -> return $ '_':rest
      Nothing -> return "_"
  ]

parseIdent :: Parser Syntax
parseIdent = IdentSyntax <$> position <*> identString

data LetType = Basic | Back

parseLet :: Parser Syntax
parseLet = do
  p <- position
  _ <- exact "let"
  _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
  i <- patternString
  _ <- whitespace0
  (ident, let_type, params, t) <- do
    mb_params <- possible parseParams
    _ <- whitespace0
    _ <- char ':'
    t <- parseTerm
    case mb_params of
      Just params -> do
        _ <- char '='
        return (i, Basic, params, buildPi p params t)
      Nothing -> do
        op <- oneOf [exact "=", exact "<-"]
        case op of
          "=" -> return (i, Basic, [], t)
          "<-" -> return (i, Back, [], t)
          _ -> error "internal error"
  val <- parseTerm
  _ <- exact "in"
  _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
  scope <- parseTerm
  return $ case let_type of
    Basic -> ImmediateAppSyntax p ident params t val scope
    Back -> AppSyntax p ManyMode val (LambdaSyntax p ManyMode ident t scope)

buildPi :: Pos -> [(BinderMode, String, Syntax)] -> Syntax -> Syntax
buildPi _p [] t = t
buildPi p [(binder_mode, x, xt)] rett = PiSyntax p binder_mode x xt rett
buildPi p ((binder_mode, x, xt):xs) rett = PiSyntax p binder_mode x xt (buildPi p xs rett)

buildLambda :: Pos -> [(BinderMode, String, Syntax)] -> Syntax -> Syntax
buildLambda _p [] e = e
buildLambda p ((binder_mode, x, xt):xs) e = LambdaSyntax p binder_mode x xt (buildLambda p xs e)

parseParens :: Parser Syntax
parseParens = do
  p <- position
  _ <- char '('
  _ <- whitespace0
  res <- possible $ do
    x <- identString
    _ <- whitespace0
    res2 <- possible $ char ':'
    case res2 of
      Just _ -> do
        t <- parseTerm
        _ <- char ')'
        _ <- whitespace0
        next <- oneOf [exact "&", exact "->", exact "=>"]
        _ <- whitespace0
        right <- parseTerm
        case next of
          "&" -> return $ IntersectionTypeSyntax p x t right
          "->" -> return $ LambdaSyntax p ManyMode x t right
          "=>" -> return $ PiSyntax p ManyMode x t right
          _ -> error "internal error"
      Nothing -> do
        _ <- whitespace0
        _ <- char ')'
        return $ IdentSyntax p x
  case res of
    Just x -> return x
    Nothing -> do
      t <- parseTerm
      _ <- char ')'
      return t

parseNat :: Parser Syntax
parseNat = NatSyntax <$> position <*> (read <$> many (satisfy isDigit))

parseNatType :: Parser Syntax
parseNatType = do
  p <- position
  _ <- exact "Nat" -- TODO: ensure no valid identifier characters immediately following
  return $ NatTypeSyntax p

parseTypeSort :: Parser Syntax
parseTypeSort = do
  p <- position
  _ <- exact "Type" -- TODO: ensure no valid identifier characters immediately following
  return $ SortSyntax p TypeSort

parseKindSort :: Parser Syntax
parseKindSort = do
  p <- position
  _ <- exact "Kind" -- TODO: ensure no valid identifier characters immediately following
  return $ SortSyntax p KindSort

parseErased :: Parser Syntax
parseErased = do
  p <- position
  _ <- char '{'
  _ <- whitespace0
  res <- possible $ do
    x <- patternString
    _ <- whitespace0
    _ <- char ':'
    return x
  let x = fromMaybe "_" res
  t <- parseTerm
  _ <- char '}'
  _ <- whitespace0
  res2 <- oneOf [exact "->", exact "=>"]
  right <- parseTerm
  case res2 of
    "->" -> return $ LambdaSyntax p ZeroMode x t right
    "=>" -> return $ PiSyntax p ZeroMode x t right
    _ -> error "internal error"

parseAbstractType :: Parser Syntax
parseAbstractType = do
  p <- position
  _ <- char '<'
  _ <- whitespace0
  res <- possible $ do
    x <- patternString
    _ <- whitespace0
    _ <- char ':'
    return x
  let x = fromMaybe "_" res
  t <- parseTerm
  _ <- char '>'
  _ <- whitespace0
  res2 <- oneOf [exact "->", exact "=>"]
  right <- parseTerm
  case res2 of
    "->" -> return $ LambdaSyntax p TypeMode x t right
    "=>" -> return $ PiSyntax p TypeMode x t right
    _ -> error "internal error"

parseJ :: Parser Syntax
parseJ = do
  p <- position
  _ <- exact "J" -- TODO: ensure no valid identifier characters immediately following
  _ <- whitespace0
  _ <- char '('
  eq <- parseTerm
  _ <- char ','
  a <- parseTerm
  _ <- char ','
  b <- parseTerm
  _ <- char ';'
  t <- parseTerm
  _ <- char ','
  predicate <- parseTerm
  _ <- char ')'
  return $ JSyntax p eq a b t predicate

parseRefl :: Parser Syntax
parseRefl = do
  p <- position
  _ <- exact "refl" -- TODO: ensure no valid identifier characters immediately following
  _ <- whitespace0
  _ <- char '('
  x <- parseTerm
  _ <- char ','
  t <- parseTerm
  _ <- char ')'
  return $ ReflSyntax p x t

parseIntersectionType :: Parser Syntax
parseIntersectionType = do
  p <- position
  _ <- char '&'
  _ <- whitespace0
  x <- patternString
  _ <- whitespace0
  _ <- char ':'
  xt <- parseTerm
  _ <- char '.'
  IntersectionTypeSyntax p x xt <$> parseTerm

parseIntersection :: Parser Syntax
parseIntersection = do
  p <- position
  _ <- char '['
  l <- parseTerm
  _ <- char ','
  r <- parseTerm
  _ <- char ';'
  _ <- whitespace0
  t <- parseTerm -- lol, this is used in the translation, but we need to polish this later
  _ <- whitespace0
  _ <- char ']'
  return $ IntersectionSyntax p l r t

parseProjection :: Parser Syntax
parseProjection = do
  p <- position
  _ <- char '.'
  n <- oneOf [char '1', char '2']
  _ <- whitespace0
  _ <- char '('
  i <- parseTerm
  _ <- char ')'
  case n of
    '1' -> return $ FstSyntax p i
    '2' -> return $ SndSyntax p i
    _ -> error "internal error"

parseCast :: Parser Syntax
parseCast = do
  p <- position
  _ <- exact "cast"
  _ <- whitespace0
  _ <- char '('
  a <- parseTerm
  _ <- char ','
  b <- parseTerm
  _ <- char ','
  t <- parseTerm
  _ <- char ')'
  return $ CastSyntax p a b t

parseExFalso :: Parser Syntax
parseExFalso = do
  p <- position
  _ <- exact "exfalso" -- TODO: ensure no valid identifier characters immediately following
  _ <- whitespace0
  _ <- char '('
  a <- parseTerm
  _ <- char ')'
  return $ ExFalsoSyntax p a

parseTermNoPostfix :: Parser Syntax
parseTermNoPostfix = do
  _ <- whitespace0
  t <- oneOf
    [ parseParens
    , parseErased
    , parseAbstractType
    , parseIntersectionType
    , parseIntersection
    , parseProjection
    , parseNat
    , parseLet
    , parseNatType
    , parseTypeSort
    , parseKindSort
    , parseJ
    , parseRefl
    , parseCast
    , parseExFalso
    , parseIdent
    ]
  _ <- whitespace0
  return t

data Postfix = AppPostfix Pos Syntax
             | ErasedAppPostfix Pos Syntax
             | AbstractTypeAppPostfix Pos Syntax
--           | MonoidPostfix Pos [Syntax]
             | ApostrophePostfix Pos Syntax
             | EqTypePostfix Pos Syntax Syntax
             | FuncTypePostfix Pos Syntax
             | IntersectionTypePostfix Pos Syntax

parseTerm :: Parser Syntax
parseTerm = do
  t <- parseTermNoPostfix
  args <- many0 $ whitespace0 *> oneOf
    [ do
      p2 <- position
      _ <- char '('
      arg <- parseTerm
      _ <- char ')'
      return $ AppPostfix p2 arg
    , do
      p2 <- position
      _ <- char '{'
      arg <- parseTerm
      _ <- char '}'
      return $ ErasedAppPostfix p2 arg
    , do
      p2 <- position
      _ <- char '<'
      arg <- parseTerm
      _ <- char '>'
      return $ AbstractTypeAppPostfix p2 arg
    {- , do
      p2 <- position
      _ <- char '['
      terms <- sepBy0 (char ',') parseTerm
      _ <- char ']'
      _ <- whitespace0
      return $ MonoidPostfix p2 terms -}
    , do
      p2 <- position
      _ <- char '\''
      ApostrophePostfix p2 <$> parseTerm
    , do
      p2 <- position
      _ <- char '='
      _ <- whitespace0
      _ <- char '['
      ty <- parseTerm
      _ <- char ']'
      flip (EqTypePostfix p2) ty <$> parseTerm
    , do
      p2 <- position
      _ <- exact "=>"
      FuncTypePostfix p2 <$> parseTerm
    , do
      p2 <- position
      _ <- char '&'
      IntersectionTypePostfix p2 <$> parseTerm
    ]
  let out = case args of
        [] -> t
        _ -> foldl' (\b a-> case a of
            AppPostfix p2 arg -> AppSyntax p2 ManyMode b arg
            ErasedAppPostfix p2 arg -> AppSyntax p2 ZeroMode b arg
            AbstractTypeAppPostfix p2 arg -> AppSyntax p2 TypeMode b arg
            {- MonoidPostfix p2 terms ->
              foldr (\term so_far->
                  AppSyntax p2
                      (AppSyntax p2
                          (AccessSyntax (stxPos b) b "Has")
                        term)
                    so_far
                ) (AccessSyntax (stxPos b) b "Empty") terms -}
            ApostrophePostfix p2 rhs -> AppSyntax p2 ManyMode b rhs
            EqTypePostfix p2 rhs ty -> EqSyntax p2 b rhs ty
            FuncTypePostfix p2 rhs -> PiSyntax p2 ManyMode "_" b rhs
            IntersectionTypePostfix p2 rhs -> IntersectionTypeSyntax p2 "_" b rhs
          ) t args
  _ <- whitespace0
  return out

parseParams :: Parser [(BinderMode, String, Syntax)]
parseParams = many $ do
    res <- oneOf [char '(', char '<', char '{']
    _ <- whitespace0
    param <- patternString
    _ <- whitespace0
    _ <- char ':'
    case res of
      '(' -> do
        t <- parseTerm
        _ <- char ')'
        return (ManyMode, param, t)
      '<' -> do
        t <- parseTerm
        _ <- char '>'
        return (TypeMode, param, t)
      '{' -> do
        t <- parseTerm
        _ <- char '}'
        return (ZeroMode, param, t)
      _ -> error "internal error"

parseDecl :: Parser (Either (String, (Syntax, Syntax)) [String])
parseDecl = do
  p <- position
  _ <- exact "def"
  _ <- whitespace -- TODO: should be not(oneOf[satisfy isAlpha, satisfy isDigit, char '_'])
  name <- identString
  mb_not_func <- possible (whitespace0 >> char ':')
  case mb_not_func of
    Just _ -> do
      t <- parseTerm
      _ <- char '='
      body <- parseTerm
      return $ Left (name, (t, body))
    Nothing -> do
      params <- parseParams
      _ <- whitespace0
      _ <- char ':'
      t <- parseTerm
      _ <- char '='
      body <- parseTerm
      let body2 = buildLambda p params body
      return $ Left (name, (t, body2))

parseFile :: Parser (Map.Map String (Syntax, Syntax), [[String]])
parseFile = do
  let parser = many $ whitespace0 *>
        parseDecl <* whitespace0
  (decls, imports) <- fmap partitionEithers parser
  return (Map.fromList decls, imports)
