module FMV where

captures :: [Int] -> Int -> Term -> Set.Set Int
captures caps depth t = case t of
  Binder _ (Lambda _) _ _ body -> Set.map (\n->n-1) $ captures caps (depth + 1) body
  Ident _ _ _ i _ ->
    if i < depth then Set.empty else Set.singleton i
  Constructor2 _ (App ManyMode) foo bar -> captures caps depth foo `Set.union` captures caps depth bar
  Constructor2 _ (App ZeroMode) foo _bar -> captures caps depth foo
  Constructor3 _ Inter l _ _ -> captures caps depth l
  Constructor1 _ Fst i -> captures caps depth i
  Constructor1 _ Snd i -> captures caps depth i
  _ -> Set.empty

lamOp :: Int -> [Word8]
lamOp n = [0, fromIntegral n]
appOp :: [Word8]
appOp = [1]
varOp :: Int -> [Word8]
varOp n = [2, fromIntegral n]
retOp :: [Word8]
retOp = [3]
litOp :: Int -> [Word8]
litOp n = [4, fromIntegral n]
capOp :: Int -> [Word8]
capOp n = [5, fromIntegral n]

codegen :: [Int] -> [Int] -> Term -> [Word8]
codegen caps kcaps t = case t of
  Binder _ (Lambda ManyMode) _ _ body ->
    let body_caps = Set.toAscList $ captures [] 1 body in
    let body_cap_indices = map (\n->fromMaybe (-1) (elemIndex (n-1) caps) + 1) body_caps in
    let body_ops = codegen body_caps kcaps body in
    concatMap capOp (reverse body_cap_indices) ++ lamOp (length body_ops + 1) ++ body_ops ++ retOp
  Binder _ (Lambda ZeroMode) _ _ body -> codegen caps kcaps body
  Ident _ _ _ i _ ->
    case elemIndex i caps of
      Just index -> varOp (index + 1)
      Nothing -> varOp 0
  Constructor2 _ (App ManyMode) foo bar ->
    let bar_caps = Set.toAscList $ captures [] 0 bar in
    codegen caps bar_caps foo ++ codegen caps kcaps bar ++ concatMap capOp kcaps ++ appOp
  Constructor2 _ (App ZeroMode) foo _bar -> codegen caps kcaps foo
  Constructor0 _ (Nat n) -> litOp n
  Constructor5 _ J _ _ _ _ _ -> lamOp 3 ++ varOp 0 ++ retOp -- J compiles to the unerased identity function
  Constructor2 _ Refl _ _ -> lamOp 3 ++ varOp 0 ++ retOp -- Refl compiles to the unerased identity function
  Constructor3 _ Inter l _ _ -> codegen caps kcaps l
  Constructor1 _ Fst i -> codegen caps kcaps i
  Constructor1 _ Snd i -> codegen caps kcaps i
  Constructor3 _ Cast a _ _ -> codegen caps kcaps a
  _ -> undefined