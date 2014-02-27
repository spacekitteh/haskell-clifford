module Paths_clifford (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,1,0,0], versionTags = []}
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/anarkistkattun/.cabal/bin"
libdir     = "/home/anarkistkattun/.cabal/lib/x86_64-linux-ghc-7.6.3/clifford-0.1.0.0"
datadir    = "/home/anarkistkattun/.cabal/share/x86_64-linux-ghc-7.6.3/clifford-0.1.0.0"
libexecdir = "/home/anarkistkattun/.cabal/libexec"
sysconfdir = "/home/anarkistkattun/.cabal/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "clifford_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "clifford_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "clifford_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "clifford_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "clifford_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
