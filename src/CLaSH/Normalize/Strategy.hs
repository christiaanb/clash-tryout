module CLaSH.Normalize.Strategy
  ( normalizeStrategy
  )
where

-- External Modules
import Language.KURE

import Debug.Trace

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Normalize.Types
import CLaSH.Normalize.Transformations
import CLaSH.Util.Core.Types
import CLaSH.Util.Core.Traverse (transformationStep,CoreGeneric(..))
import CLaSH.Util.Pretty

normalizeStrategy :: Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
normalizeStrategy = repeatR (normalizeStrategy' .+ failR "done")

normalizeStrategy' :: Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
normalizeStrategy' = extractR $ foldl1 (>->) $ map (bottomupR . tryR . promoteR . transformationStep) steps
  where
    steps = [ letRec
            , inlineTopLevel
            , inlineNonRepResult
            , knownCase
            , funSpec
            , funExtract
            , letRemoveSimple
            , letRemove
            , betaReduce
            , etaExpand
            , appProp
            , castPropagation
            , retValSimpl
            , letFlat
            , scrutSimpl
            , scrutBndrRemove
            , caseSimpl
            , caseRemove
            , appSimpl
            , letRemoveUnused
            , castSimplification
            , inlinenonrep
            ]
