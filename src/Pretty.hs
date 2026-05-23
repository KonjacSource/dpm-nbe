{-# OPTIONS_GHC -Wno-orphans #-}
module Pretty where

import Syntax 
import Context 
import Eval 
import GHC.Stack (HasCallStack)
import qualified Data.IntMap as IM


fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = fresh ns (x ++ "'")
           | otherwise = x

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec where

  piBind ns x a =
    showParen True ((x++) . (" : "++) . go letp ns a)

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var (Ix x)                -> ((ns !! x)++)

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    -- Lam ps (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
    --                                goLam ns (Lam (fresh ns -> x) t) =
    --                                  (' ':) . (x++) . goLam (x:ns) t
    --                                goLam ns t =
    --                                  (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip ("_":ns) b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (x:ns) b where
                                   goPi ns (Pi "_" a b) =
                                     (" → "++) . go appp ns a . (" → "++) . go pip ("_":ns) b
                                   goPi ns (Pi (fresh ns -> x) a b) =
                                     piBind ns x a . goPi (x:ns) b
                                   goPi ns b =
                                     (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n    = "++) . go letp ns t . ("\n;\n"++) . go letp (x:ns) u
    
    Lam ps t                  -> par p letp $ ("λ "++) . prettyPn t ns ps where 
      prettyPn t ns [] = (". "++) . go letp ns t
      prettyPn t ns (PVar (fresh ns -> x) : ps) = (x++) . (' ' :). prettyPn t (x:ns) ps
      prettyPn t ns (PRefl : ps) = ("refl "++) . prettyPn t ns ps
      prettyPn t ns (PAbs  : ps) = ("(!) " ++) . prettyPn t ns ps

    Id a x y                  -> par p appp $ ("Id "++) . go atomp ns a . (' ':) . go atomp ns x . (' ':) . go atomp ns y
    Refl                      -> ("refl"++)
    Nat                       -> ("Nat"++)
    Zero                      -> ("zero"++)
    Succ n                    -> par p appp $ ("succ "++) . go atomp ns n
    Plus m n                  -> par p appp $ ("plus "++) . go atomp ns m . (' ':) . go atomp ns n
    Bot                       -> ("⊥"++)


instance Show Tm where 
  showsPrec p = prettyTm p []

showVal :: HasCallStack => Ctx -> Val -> String
showVal ctx v = prettyTm 0 (map fst (types ctx)) (quote (lvl ctx) v) []

showCtx :: HasCallStack => Ctx -> String
showCtx ctx@Ctx{..} = unlines $ go (zip types (reverse $ sp2ls (getEnv env))) where 
  go [] = []
  go (((x, ty), v):ts) = go ts ++ pure (x ++ " : " ++ showVal ctx ty ++ " := " ++ showVal ctx v) 

showCtx' :: HasCallStack => Ctx -> String
showCtx' ctx@Ctx{..} = unlines $ go (zip types (reverse $ sp2ls (getEnv env))) where 
  go [] = []
  go (((x, ty), v):ts) = go ts ++ pure (x ++ " : " ++ showVal ctx ty ++ " := " ++ showVal ctx v) 

showSub :: HasCallStack => Ctx -> Sub -> String
showSub ctx s = unlines $ go (IM.toList $ subs s) where 
  go [] = []
  go ((x, v):xs) = (showVal ctx (VVar (Lvl x)) ++ " -* " ++ showVal ctx v) : go xs

instance Show' Ctx where 
  show' Ctx{..} = "Ctx: \n" ++ unlines (go $ zip types (sp2ls (getEnv env))) where 
    go [] = []
    go (((x, ty), v):ts) = go ts ++ pure (x ++ " : " ++ show' ty ++ " := " ++ show' v) 