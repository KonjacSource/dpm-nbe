module Eval where 

import Syntax 
import Subst 
import GHC.Stack

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

class SubAction a where 
  subst :: Sub -> a -> a

class Force a b | a -> b where
  frc :: HasCallStack => a -> b
  frcS :: HasCallStack => Sub -> a -> b

instance SubAction Sub where
  -- subst s2 s1 = s1[s2] = s1 ∘ s2 
  -- subst :: Sub Γ Δ -> Sub Δ Θ -> Sub Γ Θ
  subst s2 s1@(Sub d c s) 
    | d > cod s2 = error "sub: (co)domain mismatch"
    | otherwise = Sub (dom s1) c (go s2 s) where 
        go s2 = \case 
          Sp -> Sp 
          s :> u -> go s2 s :> subst s2 u

instance SubAction a => SubAction [a] where 
  subst s = map (subst s)

instance (SubAction a, SubAction b) => SubAction (a, b) where 
  subst s (a, b) = (subst s a, subst s b)

instance SubAction Env where
  subst s (Env vs) = Env (mapSp (subst s) vs)

instance SubAction Closure where
  subst s (Closure env t) = Closure (subst s env) t

instance SubAction Ne where 
  subst s = \case
    NSub n sb -> NSub n (subst s sb)
    n -> NSub n s

instance SubAction Val where
  subst s = \case 
    VSub v sb -> VSub v (subst s sb)
    v -> VSub v s

instance SubAction Spine where 
  subst s = \case 
    Sp -> Sp 
    sp :> v -> subst s sp :> subst s v

instance Force Res Val where 
  frc  (Res v True) = frc v
  frc  (Res v _   ) = v
  frcS s (Res v True) = frcS s v
  frcS s (Res v _   ) = v

instance Force Val Val where
  frc = \case 
    VSub v sb -> frcS sb v 
    VNe n -> frc n
    v -> v 
  
  frcS sb = \case 
    VSub v sb' -> frcS (subst sb sb') v 
    VNe n -> frcS sb n 
    VU -> VU 
    VPi x a cl -> VPi x (subst sb a) (subst sb cl)
    VId a x y -> VId (subst sb a) (subst sb x) (subst sb y)
    VRefl -> VRefl
    VNat -> VNat
    VZero -> VZero
    VSucc n -> VSucc (subst sb n)

instance Force Ne Val where 
  frc = \case 
    NSub n sb       -> frcS sb n 
    NVar v sp       -> VNe $ NVar v (frc sp)
    NLam ps n cl sp -> frc $ napp (VNe $ NLam ps n cl Sp) (frc sp)
    NPlus u v       -> frc $ plus (frc u) (frc v)

  frcS sb = \case 
    NSub n sb'      -> frcS (subst sb sb') n 
    NVar v sp       -> frc $ napp (lookupSub sb v) (frcS sb sp)
    NLam ps d cl sp -> frc $ match ps d (subst sb cl) (frcS sb sp)
    NPlus u v       -> frc $ plus (frcS sb u) (frcS sb v)

instance Force Spine Spine where 
  frc = \case 
    Sp -> Sp 
    sp :> v -> frc sp :> frc v
  
  frcS sb = \case
    Sp -> Sp 
    sp :> v -> frcS sb sp :> frcS sb v

plus :: Val -> Val -> Res 
plus m n = case m of  
  VZero   -> progress n
  VSucc m -> progress $ VSucc (frc $ plus m n)
  _ -> block $ VNe $ NPlus m n

napp :: HasCallStack => Val -> Spine -> Res
napp v sp = case frc v of 
  v | len sp == 0 -> progress v
  VNe (NVar n sp') -> block $ VNe $ NVar n (sp' +++ sp)
  VNe (NLam ps n cl sp') 
    | len sp + len sp' >= n -> match ps n cl (sp' +++ sp)
    | otherwise -> block $ VNe $ NLam ps n cl (sp' +++ sp) 
  v -> error $ "napp: impossible ++ v = " ++ show' v ++ " sp = " ++ show' sp

-- | Precondition: length of spine must be exactly the number of binders in the closure.
capp :: Lvl -> Closure -> Spine -> Val
capp n (Closure env t) sp = 
  eval (extEnv env sp) t

infixl 8 $$ 
($$) :: Closure -> Val -> Val
cl $$ v = capp 1 cl (Sp :> v)

match :: [Pn] -> Lvl -> Closure -> Spine -> Res
match ps n cl sp = go Sp (ps, sp2ls sp) where
  go :: Spine -> ([Pn], [Val]) -> Res
  go acc = \case 
    ([]  , rest) -> progress $ frc $ napp (capp n cl acc) (ls2sp rest)
    (_   , [])   -> block $ VNe $ NLam ps n cl sp
    (p:ps, v:vs) -> case (p, frc v) of
      (PVar x, v)     -> go (acc :> v) (ps, vs)
      (PRefl , VRefl) -> go acc (ps, vs)
      (PAbs  ,  _)    -> block $ VNe $ NLam ps n cl sp
      _               -> block $ VNe $ NLam ps n cl sp

-- eval :: (γ : Sub X G) -> Env G D -> Tm D -> Val X?
eval :: Env -> Tm -> Val 
eval env = \case 
  Var x       -> lookupEnv x env
  App t u     -> resVal $ napp (eval env t) (Sp :> eval env u)
  Lam ps t    -> VNe $ NLam ps (numPVars ps) (Closure env t) Sp
  Pi x a b    -> VPi x (eval env a) (Closure env b)
  Let x _ t u -> let tv = eval env t in eval (define env tv) u
  U           -> VU
  Id a x y    -> VId (eval env a) (eval env x) (eval env y)
  Refl        -> VRefl
  Nat         -> VNat
  Zero        -> VZero
  Succ n      -> VSucc (eval env n)
  Plus m n    -> resVal $ plus (eval env m) (eval env n)
  Bot         -> error "eval: impossible"

-- | Beta-eta conversion checking. Precondition: both values have the same type.
conv :: Lvl -> Val -> Val -> Bool
conv l t u = case (frc t, frc u) of
  (VU, VU) -> True
  (VPi _ a b, VPi _ a' b') ->
       conv l a a'
    && conv (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VId a x y, VId a' x' y') -> conv l a a' && conv l x x' && conv l y y'
  (VRefl, VRefl) -> True
  (VNe n, VNe n') -> convNe l n n'

  (VSub {}, _) -> error "conv: impossible"
  ( _ , VSub {}) -> error "conv: impossible"

  (VZero , VZero) -> True
  (VSucc n, VSucc n') -> conv l n n'
  (VNat  , VNat) -> True
  _ -> False

convSp :: Lvl -> Spine -> Spine -> Bool
convSp l sp sp' = case (frc sp, frc sp') of 
  (Sp, Sp) -> True
  (s :> v, s' :> v') -> convSp l s s' && conv l v v'
  _ -> False

-- | n and n' should be already forced.
convNe :: Lvl -> Ne -> Ne -> Bool
convNe l n n' = case (n, n') of
  (NVar v sp, NVar v' sp') -> v == v' && convSp l sp sp'
  (NLam ps n cl sp, NLam ps' n' cl' sp') -> 
    convCl l n cl cl' && convSp l sp sp'
  _ -> False

newVars :: Lvl -> Lvl -> Spine
newVars l n = mkSp 0 Sp where 
  mkSp i sp 
    | i == n = sp 
    | otherwise = mkSp (i + 1) (sp :> VVar (l + i))

convCl :: Lvl -> Lvl -> Closure -> Closure -> Bool
convCl l n cl1 cl2 =  conv (l + n) (capp n cl1 (newVars l n)) (capp n cl2 (newVars l n))

freeClosure :: Lvl -> Lvl -> Closure -> Val
freeClosure l n cl = (capp n cl (newVars l n))

-- Quotation 

unSubNe :: Ne -> Ne
unSubNe = \case
  NSub n s -> unSubNeS s n
  n        -> n

unSubNeS :: Sub -> Ne -> Ne
unSubNeS sub = \case
  NSub n s           -> unSubNeS (subst sub s) n
  NVar x sp          -> NVar x (subst sub sp)
  NLam ps n cl sp    -> NLam ps n (subst sub cl) (subst sub sp)
  NPlus u v          -> NPlus (subst sub u) (subst sub v)

class Quote a where 
  quote :: HasCallStack => Lvl -> a -> Tm

instance Quote Val where
  quote l n = case frc n of 
    VNe n -> quote l n
    VSub v sb -> error "quote: impossible"
    VU -> U
    VPi x a cl -> Pi x (quote l a) (quote (l + 1) (freeClosure l 1 cl))
    VId a x y -> Id (quote l a) (quote l x) (quote l y)
    VRefl -> Refl
    VNat -> Nat
    VZero -> Zero
    VSucc n -> Succ (quote l n)

instance Quote Ne where
  quote l n = case unSubNe n of 
    NSub n sb -> error "quoteNe: impossible"
    NVar v sp -> foldl App (Var (lvl2Ix l v)) (map (quote l) (sp2ls sp))
    NLam ps n cl sp -> Lam ps (quote (l + numPVars ps) (capp n cl (newVars l (numPVars ps)))) 
    NPlus u v -> Plus (quote l u) (quote l v)

nf :: Env -> Tm -> Tm 
nf e@(Env (len -> l))= quote l . eval e