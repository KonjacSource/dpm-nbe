module Subst where 

import Syntax
import GHC.Stack

lookupSub :: HasCallStack => Sub -> Lvl -> Val 
lookupSub (Sub d c s) i = go (c - i - 1, s) where 
  go = \case 
    (_, Sp) -> error "lookupSub: index out of bounds"
    (0, s :> v) -> v
    (j, s :> v) -> go (j - 1, s)

lookupSubByIx :: HasCallStack => Sub -> Ix -> Val
lookupSubByIx (Sub d c s) i = go (i, s) where 
  go = \case 
    (_, Sp) -> error "lookupSubByIx: index out of bounds"
    (0, s :> v) -> v
    (j, s :> v) -> go (j - 1, s)

-- | idSub : Sub Γ Γ
idSub :: HasCallStack => Lvl -> Sub
idSub i = Sub i i (go 0 Sp) where
  go j acc | i == j = acc
  go j acc = go (j + 1) (acc :> VVar j)

-- | emptySub : Sub Γ .
emptySub :: HasCallStack => Lvl -> Sub
emptySub d = Sub d 0 Sp
{-# inline emptySub #-}

-- | extSub : (γ : Sub Γ Δ) -> Val Γ A[γ] -> Sub Γ (Δ, A)
extSub :: HasCallStack => Sub -> Val -> Sub
extSub (Sub d c s) v = Sub d (c + 1) (s :> v)
{-# inline extSub #-}

liftSub :: HasCallStack => Sub -> Sub
liftSub (Sub d c s) = Sub (d + 1) (c + 1) (s :> VVar d)
{-# inline liftSub #-}

wkSub :: HasCallStack => Lvl -> Sub -> Sub
wkSub n s = s { dom = dom s + n }
{-# inline wkSub #-}

define :: HasCallStack =>  Env -> Val -> Env 
define (Env vs) v = Env (vs :> v)
{-# inline define #-}


-- [x ↦ v] : Sub (Γ/{x}) Γ
-- v : Val (Γ/{x}) 
insertSub :: HasCallStack => Lvl -> Lvl -> Val -> Sub 
insertSub g x v = Sub (g - 1) g (go 0 Sp) where 
  go j acc | x == j = go (j + 1) (acc :> v)
           | j == g = acc
           | otherwise = go (j + 1) (acc :> VVar j)


