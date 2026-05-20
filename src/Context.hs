{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Context where

import Syntax
import Text.Megaparsec
import Eval 

data Ctx = Ctx 
  { lvl :: Lvl
  , names :: [Name]
  , types :: [(Name, VTy)]
  , env :: Env
  , pos :: SourcePos
  }

emptyCtx :: SourcePos -> Ctx
emptyCtx = Ctx 0 [] [] emptyEnv

type M = Either (String, SourcePos)

lookupVar :: Name -> Ctx -> M (Ix, VTy)
lookupVar x Ctx {..} = go 0 x types where 
  go i x [] = Left ("unbound variable: " ++ x, pos)
  go i x ((y, ty):ys) | x == y    = Right (Ix i, ty)
                      | otherwise = go (i + 1) x ys

report :: Ctx -> String -> M a
report ctx msg = Left (msg, pos ctx)

bindCtx :: Name -> VTy -> Ctx -> Ctx
bindCtx x ~a (Ctx{..}) =
  Ctx (lvl+1) (x:names) ((x, a):types) (newVal env (VVar lvl)) pos

defineCtx :: Name -> Val -> VTy -> Ctx -> Ctx
defineCtx x ~t ~a (Ctx{..}) =
  Ctx (lvl+1) (x:names) ((x, a):types) (newVal env t) pos

instance SubAction Ctx where
  -- precondition: dom s <= lvl
  subst s (Ctx{..}) = Ctx lvl names (map (\(x, ty) -> (x, subst s ty)) types) (subst s env) pos
  -- lvl stays the same, we do not actually delete variables.

instance MonadFail (Either (String, SourcePos)) where
  fail msg = error $ "IMPOSSIBLE: " ++ msg
