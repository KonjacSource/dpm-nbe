{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
#if __GLASGOW_HASKELL__ >= 810
{-# OPTIONS_GHC -Wno-prepositive-qualified-module #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_dpm_nbe (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath




bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "C:\\Users\\86158\\temp\\elaboration-zoo\\02-typecheck-closures-debruijn\\.stack-work\\install\\b784a5d1\\bin"
libdir     = "C:\\Users\\86158\\temp\\elaboration-zoo\\02-typecheck-closures-debruijn\\.stack-work\\install\\b784a5d1\\lib\\x86_64-windows-ghc-9.10.2-cea6\\dpm-nbe-0.1.0.0-BMAMEAYmpY5CBddv17xxEP-dpm-nbe"
dynlibdir  = "C:\\Users\\86158\\temp\\elaboration-zoo\\02-typecheck-closures-debruijn\\.stack-work\\install\\b784a5d1\\lib\\x86_64-windows-ghc-9.10.2-cea6"
datadir    = "C:\\Users\\86158\\temp\\elaboration-zoo\\02-typecheck-closures-debruijn\\.stack-work\\install\\b784a5d1\\share\\x86_64-windows-ghc-9.10.2-cea6\\dpm-nbe-0.1.0.0"
libexecdir = "C:\\Users\\86158\\temp\\elaboration-zoo\\02-typecheck-closures-debruijn\\.stack-work\\install\\b784a5d1\\libexec\\x86_64-windows-ghc-9.10.2-cea6\\dpm-nbe-0.1.0.0"
sysconfdir = "C:\\Users\\86158\\temp\\elaboration-zoo\\02-typecheck-closures-debruijn\\.stack-work\\install\\b784a5d1\\etc"

getBinDir     = catchIO (getEnv "dpm_nbe_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "dpm_nbe_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "dpm_nbe_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "dpm_nbe_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "dpm_nbe_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "dpm_nbe_sysconfdir") (\_ -> return sysconfdir)



joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '\\'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/' || c == '\\'
