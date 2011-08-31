module CLaSH.Normalize.Strategy
  ( normalizeStrategy
  )
where

-- External Modules
import Language.KURE

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Normalize.Types
import CLaSH.Normalize.Transformations
import CLaSH.Util.Core.Types
import CLaSH.Util.Core.Traverse (transformationStep)

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
            , etaExpand
            , betaReduce
            , appProp
            , castPropagation
            , letRemoveSimple
            , letRemove
            , retValSimpl
            , letFlat
            , scrutSimpl
            , scrutBndrRemove
            , caseSimpl
            , caseRemove
            , inlinenonrep
            , appSimpl
            , letRemoveUnused
            , castSimplification
            ]
