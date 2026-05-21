module Syntax where 

import Text.Megaparsec
import Data.IntMap (IntMap)

-- syntax
--------------------------------------------------------------------------------

-- | De Bruijn index.
newtype Ix  = Ix { unIx :: Int } deriving (Eq, Show, Num, Ord) via Int

-- | De Bruijn level.
newtype Lvl = Lvl { unLvl :: Int } deriving (Eq, Show, Num, Ord) via Int


type Name = String

data Raw
  = RVar Name              -- x
  | RApp Raw Raw           -- t u
  | RU                     -- U
  | RLet Name Raw Raw Raw  -- let x : A = t; u
  | RPi Name Raw Raw       -- (x : A) -> B

  | RLam [Pn] Raw          -- \ p1 p2 ... -> t
  | RRefl                  -- refl
  | RId Raw Raw Raw        -- Id A u v
  | RNat                   -- Nat
  | RZero                  -- zero
  | RSucc Raw              -- succ t
  | RPlus Raw Raw          -- plus t u
  | RBot                   -- \ (!)  <===> RLam [PAbs] RBot
  | RSrcPos SourcePos Raw  -- source position for error reporting
  deriving Show

stripPos :: Raw -> Raw
stripPos = \case 
  RSrcPos _ t -> stripPos t
  RVar x -> RVar x
  RApp t u -> RApp (stripPos t) (stripPos u)
  RU -> RU
  RLet x a t u -> RLet x (stripPos a) (stripPos t) (stripPos u)
  RPi x a b -> RPi x (stripPos a) (stripPos b)
  RLam ps t -> RLam ps (stripPos t)
  RRefl -> RRefl
  RId a x y -> RId (stripPos a) (stripPos x) (stripPos y)
  RNat -> RNat
  RZero -> RZero
  RSucc n -> RSucc (stripPos n)
  RPlus m n -> RPlus (stripPos m) (stripPos n)
  RBot -> RBot

-- core syntax
------------------------------------------------------------

type Ty = Tm

data Tm
  = Var Ix
  | U
  | Let Name Ty Tm Tm
  | Pi Name Ty Ty
  | Lam [Pn] Tm
  | App Tm Tm
  | Id Tm Tm Tm 
  | Refl
  | Nat 
  | Zero 
  | Succ Tm 
  | Plus Tm Tm
  | Bot

data Pn
  = PVar Name
  | PRefl
  | PAbs

instance Show Pn where 
  show = \case 
    PVar x -> x
    PRefl -> "refl"
    PAbs -> "(!)"

-- values
------------------------------------------------------------

newtype Env = Env { getEnv :: Spine }

emptyEnv :: Env
emptyEnv = Env Sp

-- Closure Γ n = Env Γ Δ × Tm (Δ + n) ⋍ Vec n (Val Γ) -> Val Γ
-- For (γ : Sub Ξ Γ) (cl : Closure Γ n), we can apply γ to cl, (cl [γ] : Closure Ξ n) 
-- where cl [γ] := (cl.env ∘ γ, cl.tm)
-- See instance SubAction Closure
data Closure = Closure Env Tm 

instance Show Closure where
  show (Closure (Env vs) t) = "closure" 

instance Show Sub where 
  show (Sub d c s) = "sub : " ++ show d ++ " -> " ++ show c

infixl 5 :>
data Spine = Sp | Spine :> Val deriving Show

-- level indexed.
data Sub = Sub { dom :: Lvl, cod :: Lvl, subs :: IntMap Val }

type VTy = Val
data Val
  = VNe Ne 
  | VSub Val Sub 
  | VU
  | VPi Name ~VTy {-# unpack #-} Closure
  | VId VTy Val Val 
  | VRefl
  | VNat 
  | VZero 
  | VSucc Val 
  deriving Show

data Ne 
  = NSub Ne Sub
  | NVar Lvl Spine
  | NLam [Pn] Lvl {-# unpack #-} Closure Spine
  -- ^ lambda case is not stable under substitution
  | NPlus Val Val
  deriving Show

pattern VVar :: Lvl -> Val
pattern VVar v = VNe (NVar v Sp)

data Res = Res { resVal :: !Val, resProgressed :: !Bool }

block :: Val -> Res
block v = Res v False
{-# inline block #-}

progress :: Val -> Res
progress v = Res v True
{-# inline progress #-}


mapSp :: (Val -> Val) -> Spine -> Spine
mapSp f = \case 
  Sp -> Sp 
  s :> v -> mapSp f s :> f v

(+++) :: Spine -> Spine -> Spine
s1 +++ s2 = case s2 of 
  Sp -> s1
  s :> v -> (s1 +++ s) :> v

len :: Spine -> Lvl
len = \case 
  Sp -> 0
  s :> _ -> 1 + len s

sp2ls :: Spine -> [Val]
sp2ls Sp = []
sp2ls (s :> v) = sp2ls s ++ [v]

ls2sp :: [Val] -> Spine
ls2sp [] = Sp
ls2sp (v:vs) = (Sp :> v) +++ ls2sp vs

extEnv :: Env -> Spine -> Env
extEnv (Env vs) s = Env (vs +++ s)
{-# inline extEnv #-}

newVal :: Env -> Val -> Env 
newVal (Env vs) v = Env (vs :> v)
{-# inline newVal #-}

lookupEnv :: Ix -> Env -> Val 
lookupEnv i (Env vs) = go (i, vs) where 
  go = \case 
    (_, Sp) -> error "lookupEnv: index out of bounds"
    (0, s :> v) -> v
    (j, s :> v) -> go (j - 1, s)

numPVars :: [Pn] -> Lvl
numPVars = \case 
  [] -> 0
  (PVar _ : ps) -> 1 + numPVars ps
  (_ : ps) -> numPVars ps

--- roughly pretty printing

class Show' a where 
  show' :: a -> String

instance Show' Val where 
  show' = \case 
    VNe n -> show' n
    VSub v s -> show' v ++ " [" ++ show' s ++ "]"
    VU -> "U"
    VPi x a cl -> "(Pi " ++ x ++ " : " ++ show' a ++ ". " ++ show' cl ++ ")"
    VId a x y -> "(Id " ++ show' a ++ " " ++ show' x ++ " " ++ show' y ++ ")"
    VRefl -> "refl"
    VNat -> "Nat"
    VZero -> "zero"
    VSucc n -> "(succ " ++ show' n ++ ")"
    
instance Show' Ne where
  show' = \case 
    NSub n s -> show' n ++ " [" ++ show' s ++ "]"
    NVar v sp -> "lvl " ++ show v ++ " " ++ show' sp
    NLam ps n cl sp -> "(NLam " ++ show ps ++ " " ++ show n ++ " " ++ show cl ++ " " ++ show' sp ++ ")"
    NPlus m n -> "(plus " ++ show' m ++ " " ++ show' n ++ ")"

instance Show' Spine where 
  show' = show . sp2ls

instance Show' Closure where 
  show' = show 

instance Show' Sub where 
  show' Sub{..} = show dom ++ " -> " ++ show cod ++ " lvl:{" ++ show subs ++ "}" where 

