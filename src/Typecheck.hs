module Typecheck where

import Header (idx, pretty, Term, Pos, Constructor5(..), Constructor3(..), Constructor2(..), Constructor1(..), BinderMode(..), Constructor0(..), Sort(..), Term(..), Binder(..))

sortOf :: Term -> Sort
sortOf t = case t of
  Ident _ _ s _ _ -> s
  Binder _ (Lambda _) _ _ _ -> TypeSort
  Binder _ (Pi _) _ _ _ -> KindSort
  Binder _ InterT _ _ _ -> KindSort
  Constructor0 _ (Sort TypeSort) -> KindSort
  Constructor0 _ (Sort KindSort) -> undefined
  Constructor0 _ Diamond -> undefined
  Constructor0 _ NatT -> KindSort
  Constructor0 _ (Nat n) -> TypeSort
  Constructor1 _ ExFalso _ -> TypeSort
  Constructor1 _ Fst _ -> TypeSort
  Constructor1 _ Snd _ -> TypeSort
  Constructor2 _ Refl _ _ -> TypeSort
  Constructor2 _ (App _) f _ -> sortOf f
  Constructor3 _ Cast _ _ _ -> TypeSort
  Constructor3 _ Inter _ _ _ -> TypeSort
  Constructor3 _ Eq _ _ _ -> KindSort
  Constructor5 _ J _ _ _ _ _ -> TypeSort

funcTypeCodomain :: BinderMode -> Sort
funcTypeCodomain mode = case mode of
  ManyMode -> TypeSort
  TypeMode -> KindSort
  ZeroMode -> TypeSort

funcTypeDomain :: BinderMode -> Sort -> Sort
funcTypeDomain mode sort = case (mode, sort) of
  (ManyMode, _k) -> TypeSort
  (TypeMode, k) -> k
  (ZeroMode, k) -> k

toSort :: Term -> Maybe Sort
toSort t = case t of
  Constructor0 _ (Sort s) -> Just s
  _ -> Nothing

infer :: Maybe Term -> [(Pos, BinderMode, Term, Maybe Term)] -> Term -> Either String Term
infer arg gamma term = case term of
  Ident _p _mode _sort i _name ->
    case idx (reverse gamma) i of
      Just (_, _, ty, _) -> return ty
      Nothing -> Left $ "unknown identifier found during typechecking; " ++ show i
  Binder p (Lambda mode) x t e -> do
    _tt <- infer Nothing gamma t
    et <- infer Nothing ((p, mode, t, arg):gamma) e
    k <- infer Nothing gamma $ Binder p (Pi mode) x t et
    -- todo: when mode == ZeroMode, check that the erasure of e doesn't mention x
    if k == Constructor0 p (Sort $ funcTypeCodomain mode) then
      return $ Binder p (Pi mode) x t et
    else
      Left "invalid type for lambda"
  Binder p (Pi mode) _x t u -> do
    tt <- infer Nothing gamma t
    _ut <- infer Nothing ((p, mode, t, Nothing):gamma) u
    if mode == ManyMode && toSort tt /= Just TypeSort then
      Left $ "A many-mode Pi-type can only have a type as its domain: " ++ pretty tt
    else 
      return $ Constructor0 p $ Sort $ funcTypeCodomain mode
  Binder p InterT x t u -> undefined
  Constructor0 p (Sort TypeSort) -> return $ Constructor0 p (Sort KindSort)
  Constructor0 _ (Sort KindSort) -> undefined
  Constructor0 p Diamond -> undefined
  Constructor0 p NatT -> return $ Constructor0 p (Sort TypeSort)
  Constructor0 p (Nat _n) -> return $ Constructor0 p NatT
  Constructor1 p ExFalso a -> undefined
  Constructor1 p Fst a -> undefined
  Constructor1 p Snd a -> undefined
  Constructor2 p Refl a t -> undefined
  Constructor2 p (App mode) foo bar -> undefined
  Constructor3 p Cast a b e -> undefined
  Constructor3 p Inter a b t -> undefined
  Constructor3 p Eq a b t -> undefined
  Constructor5 p J a b eq at prop -> undefined

cBool :: Pos -> Term
cBool p = Binder p (Pi ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Pi ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Pi ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ZeroMode KindSort 2 "t")))
ctt :: Pos -> Term
ctt p = Binder p (Lambda ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Lambda ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Lambda ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ManyMode TypeSort 1 "x")))
cff :: Pos -> Term
cff p = Binder p (Lambda ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Lambda ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Lambda ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ManyMode TypeSort 0 "y")))
