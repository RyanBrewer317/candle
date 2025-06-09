{-# LANGUAGE GADTs #-}
module Header where

import qualified Data.Map as Map
import Data.List (intercalate)
import Data.Either (partitionEithers)
import Data.Char (isAlpha, isDigit)
import Data.Functor (($>))
import GHC.IO.Handle (hFlush)
import System.IO (stdout)
import Data.Maybe (fromMaybe)
import Control.Monad (when)
import System.Environment (getArgs)

class Pretty a where
  pretty :: a -> String

data Pos = Pos String Int Int deriving Show

instance Pretty Pos where
  pretty (Pos _ l c) = show l ++ ":" ++ show c

data BinderMode = ZeroMode | ManyMode | TypeMode deriving (Show, Eq)

data Sort = TypeSort | KindSort deriving (Show, Eq)

data Syntax = LambdaSyntax Pos BinderMode String Syntax Syntax
            | IdentSyntax Pos String
            | AppSyntax Pos BinderMode Syntax Syntax
            | ImmediateAppSyntax Pos String [(BinderMode, String, Syntax)] Syntax Syntax Syntax
            | NatSyntax Pos Int
            | NatTypeSyntax Pos
            | SortSyntax Pos Sort
            | PiSyntax Pos BinderMode String Syntax Syntax
            | JSyntax Pos Syntax Syntax Syntax Syntax Syntax
            | IntersectionTypeSyntax Pos String Syntax Syntax
            | IntersectionSyntax Pos Syntax Syntax Syntax
            | FstSyntax Pos Syntax
            | SndSyntax Pos Syntax
            | EqSyntax Pos Syntax Syntax Syntax
            | ReflSyntax Pos Syntax Syntax
            | CastSyntax Pos Syntax Syntax Syntax
            | ExFalsoSyntax Pos Syntax
            deriving Show

stxPos :: Syntax -> Pos
stxPos stx = case stx of
  LambdaSyntax p _ _ _ _ -> p
  IdentSyntax p _ -> p
  AppSyntax p _ _ _ -> p
  ImmediateAppSyntax p _ _ _ _ _ -> p
  NatSyntax p _ -> p
  NatTypeSyntax p -> p
  SortSyntax p _ -> p
  PiSyntax p _ _ _ _ -> p
  JSyntax p _ _ _ _ _ -> p
  IntersectionTypeSyntax p _ _ _ -> p
  IntersectionSyntax p _ _ _ -> p
  FstSyntax p _ -> p
  SndSyntax p _ -> p
  EqSyntax p _ _ _ -> p
  ReflSyntax p _ _ -> p
  CastSyntax p _ _ _ -> p
  ExFalsoSyntax p _ -> p

prettyParams :: [(BinderMode, String, Syntax)] -> String
prettyParams = concatMap (\(mode, x, mb_t) -> case (mode, mb_t) of
    (ManyMode, t) -> "(" ++ x ++ ": " ++ pretty t ++ ")"
    (ZeroMode, t) -> "{" ++ x ++ ": " ++ pretty t ++ "}"
    (TypeMode, t) -> "<" ++ x ++ ": " ++ pretty t ++ ">"
  )

instance Pretty Syntax where
  pretty stx = case stx of
    LambdaSyntax _ ManyMode x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")-> " ++ pretty e
    LambdaSyntax _ ZeroMode x t e -> "{" ++ x ++ ": " ++ pretty t ++ "}-> " ++ pretty e
    LambdaSyntax _ TypeMode x t e -> "<" ++ x ++ ": " ++ pretty t ++ ">-> " ++ pretty e
    IdentSyntax _ s -> s
    AppSyntax _ ManyMode f a -> "(" ++ pretty f ++ ")(" ++ pretty a ++ ")"
    AppSyntax _ ZeroMode f a -> "(" ++ pretty f ++ "){" ++ pretty a ++ "}"
    AppSyntax _ TypeMode f a -> "(" ++ pretty f ++ ")<" ++ pretty a ++ ">"
    ImmediateAppSyntax _ x params t v e -> "let " ++ x ++ prettyParams params ++ ": " ++ pretty t ++ " = " ++ pretty v ++ " in " ++ pretty e
    NatSyntax _ n -> show n
    NatTypeSyntax _ -> "Nat"
    SortSyntax _ TypeSort -> "Type"
    SortSyntax _ KindSort -> "Kind"
    PiSyntax _ ManyMode x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")=> " ++ pretty e
    PiSyntax _ ZeroMode x t e -> "{" ++ x ++ ": " ++ pretty t ++ "}=> " ++ pretty e
    PiSyntax _ TypeMode x t e -> "<" ++ x ++ ": " ++ pretty t ++ ">=> " ++ pretty e
    JSyntax _ a b c d e -> "J(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty c ++ ", " ++ pretty d ++ ", " ++ pretty e ++ ")"
    IntersectionTypeSyntax _ x t e -> "(" ++ x ++ ": " ++ pretty t ++ ")&" ++ pretty e
    IntersectionSyntax _ a b t -> "[" ++ pretty a ++ ", " ++ pretty b ++ "; " ++ pretty t ++ "]"
    FstSyntax _ a -> ".1(" ++ pretty a ++ ")"
    SndSyntax _ a -> ".2(" ++ pretty a ++ ")"
    EqSyntax _ a b t -> "(" ++ pretty a ++ ") =[" ++ pretty t ++ "] (" ++ pretty b ++ ")"
    ReflSyntax _ a t -> "refl(" ++ pretty a ++ ", " ++ pretty t ++ ")"
    CastSyntax _ a b eq -> "cast(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty eq ++ ", " ++ ")"
    ExFalsoSyntax _ a -> "exfalso(" ++ pretty a ++ ")"

data Binder where
  Lambda :: BinderMode -> Binder
  Pi :: BinderMode -> Binder
  InterT :: Binder

data Constructor0 where
  Diamond :: Constructor0
  Sort :: Sort -> Constructor0
  NatT :: Constructor0
  Nat :: Int -> Constructor0
data Constructor1 where
  Fst :: Constructor1
  Snd :: Constructor1
  ExFalso :: Constructor1
data Constructor2 where
  App :: BinderMode -> Constructor2
  Refl :: Constructor2
data Constructor3 where
  Inter :: Constructor3
  Eq :: Constructor3
  Cast :: Constructor3
data Constructor5 where
  J :: Constructor5

data Term where
  Ident :: Pos -> BinderMode -> Sort -> Int -> String -> Term
  Binder :: Pos -> Binder -> String -> Term -> Term -> Term
  Constructor0 :: Pos -> Constructor0 -> Term
  Constructor1 :: Pos -> Constructor1 -> Term -> Term
  Constructor2 :: Pos -> Constructor2 -> Term -> Term -> Term
  Constructor3 :: Pos -> Constructor3 -> Term -> Term -> Term -> Term
  Constructor5 :: Pos -> Constructor5 -> Term -> Term -> Term -> Term -> Term -> Term

instance Pretty Term where
  pretty t = case t of
    Ident _ _ _ _ x -> x
    Binder _ (Lambda ManyMode) x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")-> " ++ pretty e
    Binder _ (Lambda ZeroMode) x ty e -> "{" ++ x ++ ": " ++ pretty ty ++ "}-> " ++ pretty e
    Binder _ (Lambda TypeMode) x ty e -> "<" ++ x ++ ": " ++ pretty ty ++ ">-> " ++ pretty e
    Binder _ (Pi ManyMode) "_" a b -> "(" ++ pretty a ++ ")=> " ++ pretty b
    Binder _ (Pi ManyMode) x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")=> " ++ pretty e
    Binder _ (Pi ZeroMode) "_" a b -> "{" ++ pretty a ++ "}=> " ++ pretty b
    Binder _ (Pi ZeroMode) x ty e -> "{" ++ x ++ ": " ++ pretty ty ++ "}=> " ++ pretty e
    Binder _ (Pi TypeMode) "_" a b -> "<" ++ pretty a ++ ">=> " ++ pretty b
    Binder _ (Pi TypeMode) x ty e -> "<" ++ x ++ ": " ++ pretty ty ++ ">=> " ++ pretty e
    Binder _ InterT x ty e -> "(" ++ x ++ ": " ++ pretty ty ++ ")&(" ++ pretty e ++ ")"
    Constructor0 _ Diamond -> "<>"
    Constructor0 _ (Sort TypeSort) -> "Type"
    Constructor0 _ (Sort KindSort) -> "Kind"
    Constructor0 _ NatT -> "Nat"
    Constructor0 _ (Nat n) -> show n
    Constructor1 _ Fst a -> ".1(" ++ pretty a ++ ")"
    Constructor1 _ Snd a -> ".2(" ++ pretty a ++ ")"
    Constructor1 _ ExFalso a -> "exfalso(" ++ pretty a ++ ")"
    Constructor2 _ (App ManyMode) foo bar -> "(" ++ pretty foo ++ ")(" ++ pretty bar ++ ")"
    Constructor2 _ (App ZeroMode) foo bar -> "(" ++ pretty foo ++ "){" ++ pretty bar ++ "}"
    Constructor2 _ (App TypeMode) foo bar -> "(" ++ pretty foo ++ ")<" ++ pretty bar ++ ">"
    Constructor2 _ Refl a ty -> "refl(" ++ pretty a ++ ", " ++ pretty ty ++ ")"
    Constructor3 _ Inter a b ty -> "[" ++ pretty a ++ ", " ++ pretty b ++ "; " ++ pretty ty ++ "]"
    Constructor3 _ Eq a b ty -> "(" ++ pretty a ++ ") =[" ++ pretty ty ++ "] (" ++ pretty b ++ ")"
    Constructor3 _ Cast a b eq -> "cast(" ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty eq ++ ")"
    Constructor5 _ J eq a b ty p -> "J(" ++ pretty eq ++ ", " ++ pretty a ++ ", " ++ pretty b ++ ", " ++ pretty ty ++ ", " ++ pretty p ++ ")"

prettyContext :: [(a, Term, b)] -> String
prettyContext gamma = intercalate ", " $ map (\(_, t, _) -> pretty t) gamma

idx :: [a] -> Int -> Maybe a
idx xs i = case xs of
  [] -> Nothing
  (x:rest) -> if i == 0 then Just x else idx rest (i - 1)
