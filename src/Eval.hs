module Eval where 

import Syntax 
import Subst 
import GHC.Stack
import qualified Data.IntMap as IM

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

class SubAction a where 
  subst :: Sub -> a -> a

class Force a b | a -> b where
  frc :: HasCallStack => a -> b

substStrict :: Sub -> Val -> Val
substStrict s = \case
  VD v -> substStrict s v
  VNe n -> substStrictN s n 
  VU -> VU
  VPi x a cl -> VPi x (substStrict s a) (subst s cl)
  VId a x y -> VId (substStrict s a) (substStrict s x) (substStrict s y)
  VRefl -> VRefl
  VNat -> VNat
  VZero -> VZero
  VSucc n -> VSucc (substStrict s n)
  VBot -> VBot

substStrictSp :: Sub -> Spine -> Spine
substStrictSp s = \case 
  Sp -> Sp
  sp :> v -> substStrictSp s sp :> substStrict s v

substStrictN :: Sub -> Ne -> Val
substStrictN s = \case
  ND v -> substStrict s v
  NVar v sp -> (lookupSub s v) `napp` substStrictSp s sp
  NLam ps n cl sp -> match ps n (subst s cl) (substStrictSp s sp)
  NPlus m n -> plus (substStrict s m) (substStrict s n)

instance SubAction Sub where
  -- subst s2 s1 = s1[s2] = s1 ∘ s2 
  -- subst :: Sub Γ Δ -> Sub Δ Θ -> Sub Γ Θ
  subst s2 s1@(Sub d c s) 
    | d > cod s2 = error "sub: (co)domain mismatch"
    | otherwise = Sub 
        { dom = (dom s2)
        , cod = c
        , subs = IM.union (IM.map (subst s2) s) (subs s2) } 
        
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
    ND r -> ND (substStrict  s r) 
    n    -> ND (substStrictN s n)

instance SubAction Val where
  subst s = \case 
    VD v -> VD (substStrict s v)
    v    -> VD (substStrict s v)

instance SubAction Spine where 
  subst s = \case 
    Sp -> Sp 
    sp :> v -> subst s sp :> subst s v

instance Force Val Val where
  frc = \case 
    VD v -> frc v
    VNe n -> frc n
    v -> v 
  
instance Force Ne Val where 
  frc = \case 
    ND n            -> frc n
    NVar v sp       -> VNe $ NVar v sp
    NLam ps n cl sp
      | len sp == 0 -> VNe $ NLam ps n cl sp
      | otherwise   -> napp (VNe $ NLam ps n cl Sp) (frc sp)
    NPlus u v       -> plus (frc u) (frc v)


instance Force Spine Spine where 
  frc = \case 
    Sp -> Sp 
    sp :> v -> frc sp :> frc v
  
  -- frcS sb = \case
  --   Sp -> Sp 
  --   sp :> v -> frcS sb sp :> frcS sb v

plus :: Val -> Val -> Val 
plus m n = case m of  
  VZero   -> n
  VSucc m -> VSucc (frc $ plus m n)
  _ -> VNe $ NPlus m n

napp :: HasCallStack => Val -> Spine -> Val
napp v sp = case frc v of 
  v | len sp == 0 -> v
  VNe (NVar n sp') -> VNe $ NVar n (sp' +++ sp)
  VNe (NLam ps n cl sp') 
    | len sp + len sp' >= n -> match ps n cl (sp' +++ sp)
    | otherwise -> VNe $ NLam ps n cl (sp' +++ sp) 
  v -> error $ "napp: impossible ++ v = " ++ show' v ++ " sp = " ++ show' sp

-- | Precondition: length of spine must be exactly the number of binders in the closure.
capp :: Lvl -> Closure -> Spine -> Val
capp n (Closure env t) sp = 
  eval (extEnv env sp) t

infixl 8 $$ 
($$) :: Closure -> Val -> Val
cl $$ v = capp 1 cl (Sp :> v)

match :: [Pn] -> Lvl -> Closure -> Spine -> Val
match ps n cl sp = go Sp (ps, sp2ls sp) where
  go :: Spine -> ([Pn], [Val]) -> Val
  go acc = \case 
    ([]  , rest) -> frc $ napp (capp n cl acc) (ls2sp rest)
    (_   , [])   -> VNe $ NLam ps n cl sp
    (p:ps', v:vs') -> case (p, frc v) of
      (PVar x, v)     -> go (acc :> v) (ps', vs')
      (PRefl , VRefl) -> go acc (ps', vs')
      (PAbs  ,  _)    -> VNe $ NLam ps n cl sp
      _               -> VNe $ NLam ps n cl sp

-- eval :: Env Γ Δ -> Tm Δ -> Val Γ
eval :: Env -> Tm -> Val 
eval env = \case 
  Var x       -> lookupEnv x env
  App t u     -> napp (eval env t) (Sp :> eval env u)
  Lam ps t    -> VNe $ NLam ps (numPVars ps) (Closure env t) Sp
  Pi x a b    -> VPi x (eval env a) (Closure env b)
  Let x _ t u -> let tv = eval env t in eval (define env tv) u
  U           -> VU
  Id a x y    -> VId (eval env a) (eval env x) (eval env y)
  Refl        -> VRefl
  Nat         -> VNat
  Zero        -> VZero
  Succ n      -> VSucc (eval env n)
  Plus m n    -> plus (eval env m) (eval env n)
  Bot         -> VBot

-- | Conversion checking. Precondition: both values have the same type.
conv :: Lvl -> Val -> Val -> Bool
conv l t u = case (frc t, frc u) of
  (VU, VU) -> True
  (VPi _ a b, VPi _ a' b') ->
       conv l a a'
    && conv (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VId a x y, VId a' x' y') -> conv l a a' && conv l x x' && conv l y y'
  (VRefl, VRefl) -> True
  (VNe n, VNe n') -> convNe l n n'

  -- (VSub {}, _) -> error "conv: impossible"
  -- ( _ , VSub {}) -> error "conv: impossible"

  (VZero , VZero) -> True
  (VSucc n, VSucc n') -> conv l n n'
  (VNat  , VNat) -> True
  (VBot  , VBot) -> True
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
  (NLam ps n cl sp, NLam ps' n' cl' sp')
    | length ps == length ps' && all (uncurry comparePn) (zip ps ps') -> 
    convCl l n cl cl' && convSp l sp sp'
  (NPlus m n, NPlus m' n') -> conv l m m' && conv l n n'
  _ -> False
  where comparePn :: Pn -> Pn -> Bool
        comparePn (PVar _) (PVar _) = True
        comparePn PRefl PRefl = True
        comparePn PAbs PAbs = True
        comparePn _ _ = False

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

class Quote a where 
  quote :: HasCallStack => Lvl -> a -> Tm

instance Quote Val where
  quote l n = case frc n of 
    VNe n -> quote l n
    VD v -> quote l v
    VU -> U
    VPi x a cl -> Pi x (quote l a) (quote (l + 1) (freeClosure l 1 cl))
    VId a x y -> Id (quote l a) (quote l x) (quote l y)
    VRefl -> Refl
    VNat -> Nat
    VZero -> Zero
    VSucc n -> Succ (quote l n)
    VBot -> Bot

instance Quote Ne where
  -- n must be forced
  quote l n = case n of 
    ND n      -> quote l n
    NVar v sp -> foldl App (Var (lvl2Ix l v)) (map (quote l) (sp2ls sp))
    NLam ps n cl sp -> foldl App 
                          (Lam ps (quote (l + numPVars ps) (capp n cl (newVars l (numPVars ps)))))
                          (map (quote l) (sp2ls sp))
    NPlus u v -> Plus (quote l u) (quote l v)

nf :: Env -> Tm -> Tm 
nf e@(Env (len -> l))= quote l . eval e