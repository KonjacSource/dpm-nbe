module Elab where 

import Syntax
import Subst 
import Eval
import Context
import Pretty
import Control.Monad
import Text.Printf
import GHC.Stack

-- Unification for DPM
--------------------------------------------------------------------------------

-- Ref: Jesper Cockx. Dominique Devriese. Frank Piessens. Pattern Matching Without K 
--      Ulf Norell. Towards a Practical Programming Language Based on Dependent Type Theory
-- Note. we do "with-K" here, but it is not a problem to do "without-K" 
-- TODO: 1. Occurs Checking. need lookup the type
--       2. Limit the unifying context, 
--          only variables introduced by the current lambda-case can be unified, 
--          this also means we do not have to apply the unifier to the whole context, 
--          but only the lambda-case variables.

-- | UnifyRes Δ : Type
data UnifyRes  
  = USucc Lvl Sub 
  -- ^ USucc : (Γ : Cx) -> Sub Γ Δ -> UnifyRes Δ
  | UAbs
  -- ^ Allow inserting an absurd pattern.
  | UIDK
  -- ^ Agda would say "I am not sure if there should be a pattern refl ..."

{-

Basic Framework

unify : (Δ : Cx) -> [(Val Δ, Val Δ)] -> UnifyRes Δ
unify Δ vs = unifyS Δ Δ id vs

unifyS : (Δ Γ : Cx) -> Sub Γ Δ -> [(Val Γ, Val Γ)] -> UnifyRes Δ
unifyS Δ Γ γ [] = USucc Γ γ 
unifyS Δ Γ γ ((v1, v2) : vs) = 
  (Ξ, ɑ : Sub Ξ Γ) <- unify1 Γ v1 v2
  unifyS Δ Ξ (γ ∘ ɑ) (vs [ɑ])

unify1 : (Γ : Cx) -> Val Γ -> Val Γ -> UnifyRes Γ
unify1 Γ = \case 
  VVar x, VVar y | x == y -> USucc Γ id
  VVar x, v               -> checkOccurs >> USucc (Γ/{x}) ([x ↦ v] : Sub (Γ/{x}) Γ)
  ... 
-}

-- | unify : (Δ : Cx) -> [(Val Δ, Val Δ)] -> UnifyRes Δ
unify :: HasCallStack => Ctx -> Lvl -> [(Val, Val)] -> UnifyRes
unify ctx d vs = unifyS ctx d d (idSub d) vs

-- | unifyS : (Δ Γ : Cx) -> Sub Γ Δ -> [(Val Γ, Val Γ)] -> UnifyRes Δ
unifyS :: HasCallStack => Ctx -> Lvl -> Lvl -> Sub -> [(Val, Val)] -> UnifyRes
unifyS ctx d _ γ [] = USucc d γ
unifyS ctx d g γ ((v1, v2) : vs) = case unify1 ctx g v1 v2 of 
  USucc s ɑ  -> unifyS ctx d s (subst ɑ γ) (subst ɑ vs)
  UAbs       -> UAbs
  UIDK       -> UIDK

-- | unify1 : (Γ : Cx) -> Val Γ -> Val Γ -> UnifyRes Γ
unify1 :: HasCallStack => Ctx -> Lvl -> Val -> Val -> UnifyRes
unify1 ctx g u v = case (frc u, frc v) of 
  (VVar x, VVar y) | x == y -> USucc g (idSub g)
  (VVar x, v) -> USucc (g - 1) (insertSub g x v) -- TODO: occurs checking make sure that v : Val (Γ/{x}) 
  (v, VVar x) -> USucc (g - 1) (insertSub g x v) 

  (VRefl, VRefl) -> USucc g (idSub g)
  (VZero, VZero) -> USucc g (idSub g)
  (VSucc m, VSucc n) -> unify1 ctx g m n -- injective
  (VZero , VSucc _)  -> UAbs
  (VSucc _, VZero)   -> UAbs

  (u , v) 
    | conv g u v -> USucc g (idSub g)
    | otherwise -> UIDK


-- Type Checking
--------------------------------------------------------------------------------

check :: HasCallStack => Ctx -> Raw -> Val -> M Tm 
check ctx r ty = case (r, frc ty) of 
  (RSrcPos pos t, a) -> check (ctx {pos = pos}) t a

  (RLam ps t, ty) -> checkPM ctx ps t ty

  (RLet x a t u, a') -> do 
    a <- check ctx a VU
    let ~va = eval (env ctx) a
    t <- check ctx t va
    let ~vt = eval (env ctx) t
    u <- check (defineCtx x vt va ctx) u a'
    pure (Let x a t u)
  (RRefl, VId a x y) -> 
    if conv (lvl ctx) x y then pure Refl else 
      report ctx $ printf 
        "expecting %s equals to %s, but it is not" (showVal ctx x) (showVal ctx y)
  (r, ty) -> do
    (t, ty') <- infer ctx r
    unless (conv (lvl ctx) ty' ty) $
      report ctx
        (printf "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
            (showVal ctx ty) (showVal ctx ty'))
    pure t

i'm_not_sure :: String 
i'm_not_sure = "I am not sure if there should be a pattern '%s' for equation between %s and %s."

it_should_not_be :: String 
it_should_not_be = "It should not be '%s' for equation between %s and %s, in fact you shold try absurd pattern '%s'."

expect_an_id :: String
expect_an_id = "Expected an identity type for pattern '%s', but got:\n\n  %s"

checkPM :: HasCallStack => Ctx -> [Pn] -> Raw -> Val -> M Tm
checkPM ctx ps t ty = case (ps, frc ty) of
  ([], ty) -> 
    check ctx t ty 
  (p:ps, VPi x a b) -> 
    case p of 
    PVar x' -> do 
      let ctx' = bindCtx x' a ctx
      e <- checkPM ctx' ps t (b $$ VVar (lvl ctx))
      case e of 
        Lam ps rhs -> pure (Lam (p : ps) rhs)
        _ | null ps -> pure $ Lam [p] e
          | otherwise -> error $ "impossible : " ++ show e 
    PRefl -> case frc a of 
      VId a x y -> case unify ctx (lvl ctx) [(x, y)] of
        USucc _ sub -> do 
          e <- checkPM (subst sub ctx) ps t (subst sub b $$ VRefl)
          case e of 
            Lam ps rhs -> pure (Lam (p : ps) rhs)
            _ | null ps -> pure $ Lam [p] e
              | otherwise -> error $ "impossible : " ++ show e 
        UAbs      -> report ctx $ printf 
          it_should_not_be ("refl" :: String) (showVal ctx x) (showVal ctx y) ("!" :: String)
        UIDK      -> report ctx $ printf i'm_not_sure ("refl" :: String) (showVal ctx x) (showVal ctx y)
      _ -> report ctx $ printf expect_an_id ("refl" :: String) (showVal ctx a)
    PAbs -> case frc a of 
      VId a x y -> case unify ctx (lvl ctx) [(x, y)] of
        USucc _ sub -> report ctx $ printf 
          it_should_not_be ("(!)" :: String) (showVal ctx x) (showVal ctx y) ("refl" :: String)
          (showVal ctx x) (showVal ctx y) 
        UAbs     -> case (ps, t) of 
          ([], RBot) -> pure (Lam [PAbs] Bot) 
          _ -> report ctx $ printf 
            "It's absurd pattern, you should have nothing on the right hand side."
        UIDK     -> report ctx $ printf 
          i'm_not_sure ("(!)" :: String) (showVal ctx x) (showVal ctx y)
      _ -> report ctx $ printf expect_an_id ("(!)" :: String) (showVal ctx a)
  _ -> report ctx "Too many patterns."

infer :: HasCallStack => Ctx -> Raw -> M (Tm, Val)
infer ctx = \case 
  RSrcPos pos t -> infer (ctx {pos = pos}) t

  RVar x -> do 
    (ix, ty) <- lookupVar x ctx
    pure (Var ix, ty)

  RU -> pure (U, VU) 

  RApp t u -> do
    (t, tty) <- infer ctx t
    case tty of
      VPi _ a b -> do
        u <- check ctx u a
        pure (App t u, b $$ eval (env ctx) u)   -- t u : B[x |-> u]
      tty ->
        report ctx $ "Expected a function type, instead inferred:\n\n  " ++ showVal ctx tty

  RLam{} -> report ctx "Can't infer type for lambda expression"

  RPi x a b -> do
    a <- check ctx a VU
    b <- check (bindCtx x (eval (env ctx) a) ctx) b VU
    pure (Pi x a b, VU)

  RLet x ty t u -> do
    ty <- check ctx ty VU
    let ~vty = eval (env ctx) ty
    t <- check ctx t vty
    let ~vt = eval (env ctx) t
    (u, uty) <- infer (defineCtx x vt vty ctx ) u
    pure (Let x ty t u, uty)

  RRefl -> report ctx "Can't infer type for refl"
  RId a x y -> do
    a <- check ctx a VU
    let va = eval (env ctx) a
    x <- check ctx x va
    y <- check ctx y va
    pure (Id a x y, VU)
  RNat -> pure (Nat, VU)
  RZero -> pure (Zero, VNat)
  RSucc n -> do
    n <- check ctx n VNat
    pure (Succ n, VNat)
  RPlus m n -> do
    m <- check ctx m VNat
    n <- check ctx n VNat
    pure (Plus m n, VNat)
  RBot -> error "impossible"

-----------------------------------------------------------------

