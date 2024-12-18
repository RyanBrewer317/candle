{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_candle (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "candle"
version :: Version
version = Version [0,1,0,0] []

synopsis :: String
synopsis = "a Cedille for the FVM"
copyright :: String
copyright = ""
homepage :: String
homepage = "ryanbrewer.dev"
