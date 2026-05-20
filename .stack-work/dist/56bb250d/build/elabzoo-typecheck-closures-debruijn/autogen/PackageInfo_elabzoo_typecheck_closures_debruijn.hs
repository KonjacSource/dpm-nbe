{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_elabzoo_typecheck_closures_debruijn (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "elabzoo_typecheck_closures_debruijn"
version :: Version
version = Version [0,1,0,0] []

synopsis :: String
synopsis = ""
copyright :: String
copyright = "2019 Andr\225s Kov\225cs"
homepage :: String
homepage = "https://github.com/AndrasKovacs/elaboration-zoo#readme"
