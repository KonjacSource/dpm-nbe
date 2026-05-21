module Subst where 

import Syntax
import GHC.Stack
import qualified Data.IntMap as IM

lookupSub :: HasCallStack => Sub -> Lvl -> Val 
lookupSub (Sub d c s) i = case IM.lookup (unLvl i) s of 
  Nothing -> VVar i
  Just v -> v

emptySubMap :: IM.IntMap Val
emptySubMap = IM.empty

-- | idSub : Sub Γ Γ
idSub :: HasCallStack => Lvl -> Sub
idSub i = Sub i i emptySubMap
{-# inline idSub #-}

-- | emptySub : Sub Γ .
emptySub :: HasCallStack => Lvl -> Sub
emptySub d = Sub d 0 emptySubMap
{-# inline emptySub #-}

wkSub :: HasCallStack => Lvl -> Sub -> Sub
wkSub n s = undefined
{-# inline wkSub #-}

define :: HasCallStack =>  Env -> Val -> Env 
define (Env vs) v = Env (vs :> v)
{-# inline define #-}


-- [x ↦ v] : Sub (Γ/{x}) Γ
-- v : Val (Γ/{x}) 
insertSub :: HasCallStack => Lvl -> Lvl -> Val -> Sub 
insertSub g x v = Sub (g - 1) g (IM.singleton (unLvl x) v)
{-# inline insertSub #-}