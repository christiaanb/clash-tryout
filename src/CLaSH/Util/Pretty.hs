module CLaSH.Util.Pretty
  ( module CLaSH.Util.Core.Pretty
  , pprString
  )
where
  
-- GHC API
import Outputable (Outputable, showSDoc, ppr)

-- Internal Modules
import CLaSH.Util.Core.Pretty (pprBinding)

pprString :: (Outputable x) => x -> String
pprString = showSDoc . ppr
