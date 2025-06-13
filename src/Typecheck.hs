module Typecheck where

import Header (idx, pretty, Term, Pos, Constructor5(..), Constructor3(..), Constructor2(..), Constructor1(..), BinderMode(..), Constructor0(..), Sort(..), Term(..), Binder(..))
import Debug.Trace

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
  Constructor0 _ (Nat _n) -> TypeSort
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

shift :: Int -> Int -> Term -> Term
shift depth amt t = 
  let s = shift depth amt in
  case t of
    Ident p mode sort i name -> 
      if i >= depth then
        Ident p mode sort (i + amt) name
      else t
    Binder p b x e1 e2 -> Binder p b x (s e1) (shift (depth + 1) amt e2)
    Constructor0 _ _ -> t
    Constructor1 p c e -> Constructor1 p c (s e)
    Constructor2 p c e1 e2 -> Constructor2 p c (s e1) (s e2)
    Constructor3 p c e1 e2 e3 -> Constructor3 p c (s e1) (s e2) (s e3)
    Constructor5 p c e1 e2 e3 e4 e5 -> Constructor5 p c (s e1) (s e2) (s e3) (s e4) (s e5)

subst :: Int -> Term -> Term -> Term
subst depth lil big = 
  let s = subst depth lil in
  case big of
    Ident _p _mode _sort i _name -> if i == depth then lil else big
    Binder p b x t e -> Binder p b x (s t) (subst depth (shift depth 1 lil) e)
    Constructor0 _ _ -> big
    Constructor1 p c e -> Constructor1 p c (s e)
    Constructor2 p c e1 e2 -> Constructor2 p c (s e1) (s e2)
    Constructor3 p c e1 e2 e3 -> Constructor3 p c (s e1) (s e2) (s e3)
    Constructor5 p c e1 e2 e3 e4 e5 -> Constructor5 p c (s e1) (s e2) (s e3) (s e4) (s e5)

alphaEq :: Int -> Term -> Term -> Bool
alphaEq depth expr1 expr2 = 
  let al = alphaEq depth in
  case (expr1, expr2) of
    (Ident _ _ _ i _, Ident _ _ _ j _) -> i == j
    (Binder _ b1 _ t1 u1, Binder _ b2 _ t2 u2) -> b1 == b2 && al t1 t2 && alphaEq (depth + 1) u1 (subst depth t1 u2)
    (Constructor0 _ k1, Constructor0 _ k2) -> k1 == k2
    (Constructor1 _ k1 a1, Constructor1 _ k2 a2) -> k1 == k2 && al a1 a2
    (Constructor2 _ k1 a1 b1, Constructor2 _ k2 a2 b2) -> k1 == k2 && al a1 a2 && al b1 b2
    (Constructor3 _ k1 a1 b1 c1, Constructor3 _ k2 a2 b2 c2) -> k1 == k2 && al a1 a2 && al b1 b2 && al c1 c2
    (Constructor5 _ k1 a1 b1 c1 d1 e1, Constructor5 _ k2 a2 b2 c2 d2 e2) -> k1 == k2 && al a1 a2 && al b1 b2 && al c1 c2 && al d1 d2 && al e1 e2
    (_, _) -> False

normalize :: [(Pos, BinderMode, Term, Maybe Term)] -> Term -> Term
normalize gamma e = 
  let n = normalize gamma in
  case e of
    Ident _ _ _ i _ -> 
      case idx gamma i of
        Just (_, _, _, Just e2) -> e2
        _ -> Debug.Trace.trace (show (map (\(_, _, ty, mbe)->(pretty ty, fmap pretty mbe)) gamma)) e
    Binder p InterT x a b -> 
      let a2 = n a in
        Binder p InterT x a2 (normalize ((p, TypeMode, a2, Nothing):gamma) b)
    Binder {} -> e
    Constructor0 _ _ -> e
    Constructor1 p c e2 -> Constructor1 p c $ n e2
    Constructor2 p (App m) foo bar ->
      case n foo of
        Binder _ (Lambda _) _ _ body -> n (shift (length gamma) (-1) $ subst (length gamma) (n bar) body)
        foo2 -> Constructor2 p (App m) foo2 (n bar)
    Constructor2 p c e2 e3 -> Constructor2 p c (n e2) (n e3)
    Constructor3 p c e2 e3 e4 -> Constructor3 p c (n e2) (n e3) (n e4)
    Constructor5 p c e2 e3 e4 e5 e6 -> Constructor5 p c (n e2) (n e3) (n e4) (n e5) (n e6)

eq :: [(Pos, BinderMode, Term, Maybe Term)] -> Term -> Term -> Bool
eq gamma e1 e2 = alphaEq (length gamma) (normalize gamma e1) (normalize gamma e2)

infer :: [Maybe Term] -> [(Pos, BinderMode, Term, Maybe Term)] -> Term -> Either String Term
infer psi gamma term = -- Debug.Trace.trace (pretty term ++ ", " ++ show (map (\(_, _, ty, mbe)->(pretty ty, fmap pretty mbe)) gamma)) $ 
  case term of
    Ident _p _mode _sort i _name ->
      case idx (reverse gamma) i of
        Just (_, _, ty, _) -> return ty
        Nothing -> Left $ "unknown identifier found during typechecking; " ++ show i
    Binder p (Lambda mode) x t e -> do
      _tt <- infer [] gamma t
      let (arg, psi2) = case psi of
            (a : psi3) -> (a, psi3)
            [] -> (Nothing, [])
      et <- infer psi2 ((p, mode, t, arg):gamma) e
      k <- infer [] gamma $ Binder p (Pi mode) x t et
      -- todo: when mode == ZeroMode, check that the erasure of e doesn't mention x
      if k == Constructor0 p (Sort $ funcTypeCodomain mode) then
        return $ Binder p (Pi mode) x t et
      else
        Left "invalid type for lambda"
    Binder p (Pi mode) _x t u -> do
      tt <- infer [] gamma t
      _ut <- infer [] ((p, mode, t, Nothing):gamma) u
      if mode == ManyMode && toSort tt /= Just TypeSort then
        Left $ "A many-mode Pi-type can only have a type as its domain: " ++ pretty tt
      else 
        return $ Constructor0 p $ Sort $ funcTypeCodomain mode
    Binder p InterT _x t u -> do
      tt <- infer [] gamma t
      _ut <- infer [] ((p, TypeMode, tt, Nothing):gamma) u
      return $ Constructor0 p (Sort TypeSort)
    Constructor0 p (Sort TypeSort) -> return $ Constructor0 p (Sort KindSort)
    Constructor0 _ (Sort KindSort) -> undefined
    Constructor0 _p Diamond -> undefined
    Constructor0 p NatT -> return $ Constructor0 p (Sort TypeSort)
    Constructor0 p (Nat _n) -> return $ Constructor0 p NatT
    Constructor1 p ExFalso a -> do
      at <- infer [] gamma a
      if eq gamma at (Constructor3 p Eq (ctt p) (cff p) (cBool p)) then
        return $ Binder p (Pi ZeroMode) "$x" (Constructor0 p (Sort TypeSort)) (Ident p ZeroMode KindSort (length gamma) "$x")
      else
        Left "Type mismatch, expected tt=ff"
    Constructor1 _p Fst a -> do
      at <- infer [] gamma a
      case at of
        Binder _ InterT _ t _u -> return t
        _ -> Left $ "Fst on non-intersection " ++ pretty at
    Constructor1 _p Snd a -> do
      at <- infer [] gamma a
      case at of
        Binder _ InterT _ t u -> return $ subst (length gamma) t (shift (length gamma) 1 u)
        _ -> Left $ "Snd on non-intersection " ++ pretty at
    Constructor2 p Refl a t -> do
      at <- infer [] gamma a
      _tt <- infer [] gamma t
      return $ Constructor3 p Eq a a at
    Constructor2 _p (App mode) foo bar -> do
      foot <- infer (Just bar : psi) gamma foo
      bart <- infer [] gamma bar
      case foot of
        Binder _ (Pi mode2) _ a b -> 
          if mode == mode2 then
            if eq gamma a bart then
              return $ subst (length gamma) bar b
            else
              Left $ "type mismatch: `" ++ pretty a ++ "`, `" ++ pretty bart ++ "`"
          else
            Left $ "mode mismatch: " ++ show mode ++ ", " ++ show mode2
        _ -> Left $ "calling non-function of type " ++ pretty foot
    Constructor3 p Cast a b e -> do
      at <- infer [] gamma a
      bt <- infer [] gamma b
      et <- infer [] gamma e
      case bt of
        Binder _ InterT _ t _u -> 
          case et of
            Constructor3 _ Eq l r lt -> 
              if eq gamma at t && eq gamma a l && eq gamma (Constructor1 p Fst b) r && eq gamma at lt then
                return bt
              else Left $ "invalid cast with `" ++ pretty bt ++ "` and `" ++ pretty et ++ "`"
            _ -> Left $ "invalid cast: expected equality, got " ++ pretty et
        _ -> Left $ "invalid cast: expected intersection, got " ++ pretty bt
    Constructor3 _p Inter a b t -> do
      _tt <- infer [] gamma t
      at <- infer [] gamma a
      bt <- infer [] gamma b
      case t of
        Binder _ InterT _ l r -> 
          -- todo: check erasure-equality
          if eq gamma at l && eq gamma bt (subst (length gamma) a r) then
            return t
          else 
            Left $ "invalid intersection with types `" ++ pretty at ++ "`, `" ++ pretty bt ++ "`, `" ++ pretty t ++ "`"
        _ -> Left $ "Binder annotation isn't an intersection type: " ++ pretty t
    Constructor3 p Eq a b t -> do
      tt <- infer [] gamma t
      at <- infer [] gamma a
      bt <- infer [] gamma b
      if toSort tt == Just TypeSort then
        if eq gamma at t && eq gamma bt t then
          return $ Constructor0 p (Sort TypeSort)
        else Left $ "mismatched types in equality: `" ++ pretty at ++ "`, `" ++ pretty bt ++ "`, `" ++ pretty t ++ "`"
      else Left "Equality types must be between types"
    Constructor5 p J a b e at prop -> do
      at2 <- infer [] gamma a
      bt <- infer [] gamma b
      et <- infer [] gamma e
      att <- infer [] gamma at
      propt <- infer [] gamma prop
      case et of
        Constructor3 _ Eq l r t ->
          case propt of
            Binder _ (Pi TypeMode) _ at3 (Binder _ (Pi TypeMode) _ (Constructor3 _ Eq a2 (Ident _ _ _ i _) at4) (Constructor0 _ (Sort TypeSort))) ->
              if toSort att == Just TypeSort && eq gamma a l && eq gamma b r && eq gamma at t && eq gamma at bt && eq gamma at at2 && eq gamma at at3 && eq gamma at at4 && eq gamma a a2 && i == length gamma + 2 then
                return $ Binder p (Pi ManyMode) "$p" (Constructor2 p (App TypeMode) (Constructor2 p (App TypeMode) prop a) (Constructor2 p Refl a at)) (Constructor2 p (App TypeMode) (Constructor2 p (App TypeMode) prop b) et)
              else
                Left $ "invalid types for J `" ++ pretty et ++ "`, `" ++ pretty propt ++ "`"
            _ -> Left $ "Ill-typed proposition in J: `" ++ pretty propt ++ "`"
        _ -> Left $ "Expected equality for J, got " ++ pretty et

cBool :: Pos -> Term
cBool p = Binder p (Pi ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Pi ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Pi ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ZeroMode KindSort 2 "t")))
ctt :: Pos -> Term
ctt p = Binder p (Lambda ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Lambda ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Lambda ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ManyMode TypeSort 1 "x")))
cff :: Pos -> Term
cff p = Binder p (Lambda ZeroMode) "t" (Constructor0 p (Sort TypeSort)) (Binder p (Lambda ManyMode) "x" (Ident p ZeroMode KindSort 0 "t") (Binder p (Lambda ManyMode) "y" (Ident p ZeroMode KindSort 1 "t") (Ident p ManyMode TypeSort 0 "y")))
