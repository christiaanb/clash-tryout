module CLaSH.Desugar.Strategy
  ( desugarStrategy
  )
where

-- External Modules
import Language.KURE

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Desugar.Types
import CLaSH.Desugar.Transformations
import CLaSH.Util.Core.Types
import CLaSH.Util.Core.Traverse (transformationStep)

desugarStrategy :: Rewrite DesugarSession [CoreContext] CoreSyn.CoreExpr
desugarStrategy = repeatR (desugarStrategy' .+ failR "done")

desugarStrategy' :: Rewrite DesugarSession [CoreContext] CoreSyn.CoreExpr
desugarStrategy' = extractR $ topdownR $ foldl1 (>->) $ map (tryR . promoteR . transformationStep) steps
  where
    steps = [ inlineArrowBndr            
            , componentDesugar
            , arrDesugar
            , returnADesugar
            , hooksDesugar
            , firstDesugar
            ]