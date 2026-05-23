module Main where

import Syntax
import Eval 
import Context
import Elab 
import Parse
import Prelude hiding (lookup)
import System.Environment
import Text.Megaparsec
import Text.Printf

-- examples
--------------------------------------------------------------------------------

ex0 = main' "nf" $ unlines [
  "let sym : (A : U) (a b : A) -> Id A a b -> Id A b a =",
  "  λ A a b refl . refl; U"
  ]

ex1 = main' "nf" $ unlines [
  "let trans : (A : U) (a b c : A) -> Id A a b -> Id A b c -> Id A a c =",
  " λ A a b c refl refl . refl; U"
  ]

ex2 = main' "nf" $ unlines [
  "let cong : (A B : U) (f : A -> B) (a b : A) -> Id A a b -> Id B (f a) (f b) =",
  " λ A B f a b refl . refl; U"
  ]

ex3 = main' "nf" $ unlines [
  "let H : (m n : Nat) -> Id Nat n (plus m zero) -> Id Nat m zero -> Id Nat n zero =",
  " λ m n refl refl . refl; U"
  ]

ex4 = main' "nf" $ unlines [
  "let C : (A : U) -> Id Nat (suc zero) zero -> A = ",
  " λ A (!); U"
  ]


genTransN :: Int -> String 
genTransN n = "let trans" 
          ++ show n ++ " : (A : U) " ++ binders ++ args ++ retType ++ " = " 
          ++ " λ A " ++ vars ++ refls ++ " . refl; U" where 
  binders = concat [ "(a" ++ show i ++ " : A) " | i <- [1..n] ]
  args = concat [ "-> Id A a" ++ show i ++ " a" ++ show (i + 1) ++ " " | i <- [1..n-1] ]
  retType = "-> Id A a1 a" ++ show n
  vars = concat [ "a" ++ show i ++ " " | i <- [1..n] ]
  refls = concat [ "refl " | i <- [1..n-1] ]

writeTransNAgda :: Int -> IO ()
writeTransNAgda n = writeFile "Test.agda" $ genTransNAgda n

genTransNAgda :: Int -> String
genTransNAgda n = agdaId ++ "\ntrans" ++ show n ++ " : {A : Set} " ++ binders ++ args ++ retType ++ "\n" 
            ++ "trans" ++ show n ++ " {A} " ++ vars ++ refls ++ " = refl" where
  agdaId = unlines [
    "data Id (A : Set) (x : A) : A -> Set where",
    "  refl : Id A x x"
    ]
  binders = concat [ "(a" ++ show i ++ " : A) " | i <- [1..n] ]
  args = concat [ "-> Id A a" ++ show i ++ " a" ++ show (i + 1) ++ " " | i <- [1..n-1] ]
  vars = concat [ "a" ++ show i ++ " " | i <- [1..n] ]
  refls = concat [ "refl " | i <- [1..n-1] ]
  retType = "-> Id A a1 a" ++ show n

exTransn :: Int -> IO ()
exTransn n = (main' "nf" $ genTransN n) >> putStrLn "done."

-- main
--------------------------------------------------------------------------------

displayError :: String -> (String, SourcePos) -> IO ()
displayError file (msg, SourcePos path (unPos -> linum) (unPos -> colnum)) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

helpMsg = unlines [
  "usage: elabzoo-typecheck-closures-debruijn [--help|nf|type]",
  "  --help : display this message",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, file) <- getRaw
      case infer (emptyCtx (initialPos file)) t of
        Left err -> displayError file err
        Right (t, a) -> do
          print $ nf emptyEnv t
          putStrLn "  :"
          print $ quote 0 a
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCtx (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> print $ quote 0 a
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)