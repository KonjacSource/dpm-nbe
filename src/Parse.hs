module Parse where

import Syntax
import Text.Megaparsec
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void
import Data.Char
import Control.Monad
import System.Exit


type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
pArrow   = symbol "→" <|> symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U" || x == "refl" || x == "Nat" || x == "zero" || x == "suc" || x == "plus" || x == "Id"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Raw
pAtom =
      withPos (
        (RVar <$> pIdent) 
        <|> (RU <$ symbol "U")
        <|> (RRefl <$ symbol "refl")
        <|> (RNat <$ symbol "Nat")
        <|> (RZero <$ symbol "zero")
        <|> symbol "suc" *> (RSucc <$> pAtom)
        <|> symbol "plus" *> (RPlus <$> pAtom <*> pAtom)
        <|> symbol "Id"   *> (RId <$> pAtom <*> pAtom <*> pAtom)
      )
  <|> parens pRaw

pBinder = pIdent <|> symbol "_"
pSpine  = foldl1 RApp <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  ps <- some pPn
  absL ps <|> normL ps 
  where 
    absL ps = do
      symbol "(!)"
      pure $ RLam (ps ++ [PAbs]) RBot
    normL ps = do
      char '.'
      t <- pRaw
      pure $ RLam ps t

pPn :: Parser Pn
pPn = (PRefl <$ symbol "refl") <|> (PVar <$> pIdent) 



pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" sp <$> pRaw

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol "="
  t <- pRaw
  symbol ";"
  u <- pRaw
  pure $ RLet x a t u

pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)
pSrc = ws *> pRaw <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t -> do 
      -- putStrLn "Parsed successfully:"
      -- print $ stripPos t
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm   <- parseString file
  pure (tm, file)

{-

"sym" 
(RPi "A" RU (RPi "a" (RVar "A") (RPi "b" (RVar "A") 
  (RPi "_" (RId (RVar "A") (RVar "a") (RVar "b")) (RId (RVar "A") (RVar "b") (RVar "a")))))) 

(RLam [PVar "A",PVar "a",PVar "b",PRefl] RRefl) 

-}