module CLaSH.Util.Pretty
  ( module CLaSH.Util.Pretty.Core
  , pprString
  )
where

-- GHC API
import Outputable (Outputable, showSDocDump, showSDoc, ppr)

-- Internal Modules
import CLaSH.Util.Pretty.Core
import CLaSH.Util.Pretty.CoreHW

pprString :: (Outputable x) => x -> String
pprString = showSDoc . ppr
