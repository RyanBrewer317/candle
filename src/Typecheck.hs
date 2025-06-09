module Typecheck where

import Header (idx, Term, Pos, Constructor5(..), Constructor3(..), Constructor2(..), Constructor1(..), BinderMode(..), Constructor0(..), Sort(..), Term(..), Binder(..))

infer :: Maybe Term -> [(Pos, BinderMode, Term, Maybe Term)] -> Term -> Either String Term
infer arg gamma term = case term of
  Ident _p _mode _sort i _name -> 
    case idx (reverse gamma) i of
      Just (_, _, ty, _) -> return ty
      Nothing -> Left $ "unknown identifier found during typechecking; " ++ show i
  Binder p (Lambda mode) x t e -> do
    tt <- infer Nothing gamma t
    et <- infer Nothing ((p, mode, t, arg):gamma) e
    k <- infer Nothing gamma $ Binder p (Pi mode) x tt et
    -- todo: when mode == ZeroMode, check that the erasure of e doesn't mention x
    if sortOf gamma k == funcTypeCodomain mode then 
      return $ Binder p (Pi mode) x tt et
    else
      Left "invalid type for lambda"
  Binder p (Pi mode) x t u -> undefined
  Binder p InterT x t u -> undefined
  Constructor0 p (Sort TypeSort) -> return $ Constructor0 p (Sort KindSort)
  Constructor0 _ (Sort KindSort) -> undefined
  Constructor0 p Diamond -> undefined
  Constructor0 p NatT -> undefined
  Constructor0 p (Nat n) -> undefined
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
