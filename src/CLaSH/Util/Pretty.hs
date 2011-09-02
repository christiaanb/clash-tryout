module CLaSH.Util.Pretty
  ( module CLaSH.Util.Pretty.Core
  , pprString
  )
where
  
-- GHC API
import Outputable (Outputable, showSDoc, ppr)

-- Internal Modules
import CLaSH.Util.Pretty.Core

pprString :: (Outputable x) => x -> String
pprString = showSDoc . ppr
