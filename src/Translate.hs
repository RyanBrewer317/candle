module Translate where

import Header (Term, Syntax(..), Constructor5(..), Constructor3(..), Constructor2(..), Constructor1(..), BinderMode(..), Constructor0(..), Sort(..), Term(..), Binder(..))
import qualified Data.Map as Map

translate :: Sort -> Int -> Map.Map String (BinderMode, Int) -> Syntax -> Either String Term
translate k l modes s = case s of
  IdentSyntax p name -> do
    case Map.lookup name modes of
      Just (mode, lvl) -> return $ Ident p mode k lvl name
      Nothing -> Left $ "unknown identifier " ++ name
  LambdaSyntax p mode x t e -> do
    t2 <- translate TypeSort l modes t
    e2 <- translate k (l + 1) (Map.insert x (mode, l) modes) e
    return $ Binder p (Lambda mode) x t2 e2
  AppSyntax p mode foo bar -> do
    foo2 <- translate k l modes foo
    bar2 <- translate k l modes bar
    return $ Constructor2 p (App mode) foo2 bar2
  ImmediateAppSyntax _p _x _params _t _v _e -> undefined
  NatSyntax p n -> return $ Constructor0 p (Nat n)
  NatTypeSyntax p -> return $ Constructor0 p NatT
  SortSyntax p s2 -> return $ Constructor0 p (Sort s2)
  PiSyntax p mode x t u -> do
    t2 <- translate KindSort l modes t
    u2 <- translate KindSort (l + 1) (Map.insert x (mode, l) modes) u
    return $ Binder p (Pi mode) x t2 u2
  JSyntax p eq a b at prop -> do
    eq2 <- translate TypeSort l modes eq
    a2 <- translate TypeSort l modes a
    b2 <- translate TypeSort l modes b
    at2 <- translate KindSort l modes at
    prop2 <- translate KindSort l modes prop
    return $ Constructor5 p J eq2 a2 b2 at2 prop2
  IntersectionTypeSyntax p x a b -> do
    a2 <- translate KindSort l modes a
    b2 <- translate KindSort (l + 1) (Map.insert x (TypeMode, l) modes) b
    return $ Binder p InterT x a2 b2
  IntersectionSyntax p a b t -> do
    a2 <- translate TypeSort l modes a
    b2 <- translate TypeSort l modes b
    t2 <- translate KindSort l modes t
    return $ Constructor3 p Inter a2 b2 t2
  FstSyntax p a -> Constructor1 p Fst <$> translate TypeSort l modes a
  SndSyntax p a -> Constructor1 p Snd <$> translate TypeSort l modes a
  EqSyntax p a b t -> do
    a2 <- translate TypeSort l modes a
    b2 <- translate TypeSort l modes b
    t2 <- translate KindSort l modes t
    return $ Constructor3 p Eq a2 b2 t2
  ReflSyntax p a t -> do
    a2 <- translate TypeSort l modes a
    t2 <- translate KindSort l modes t
    return $ Constructor2 p Refl a2 t2
  CastSyntax p a b eq -> do
    a2 <- translate TypeSort l modes a
    b2 <- translate TypeSort l modes b
    eq2 <- translate TypeSort l modes eq
    return $ Constructor3 p Cast a2 b2 eq2
  ExFalsoSyntax p a -> Constructor1 p ExFalso <$> translate TypeSort l modes a
