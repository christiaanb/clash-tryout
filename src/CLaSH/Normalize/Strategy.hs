module CLaSH.Normalize.Strategy
  ( normalizeStrategy
  )
where

-- External Modules
import Language.KURE (Rewrite, repeatR, (.+), failR, extractR, (>->), 
  bottomupR, tryR, promoteR)

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Normalize.Types
import CLaSH.Normalize.Transformations
import CLaSH.Util.Core (CoreContext, transformationStep)

normalizeStrategy ::
  Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
normalizeStrategy = repeatR (normalizeStrategy' .+ failR "done")

normalizeStrategy' ::
  Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
normalizeStrategy' = extractR $ foldl1 (>->) $ map (bottomupR . tryR . promoteR . transformationStep) steps
  where
    steps = [ inlineTopLevel
            , inlineNonRepResult
            , knownCase
            , funSpec
            , funExtract
            , etaExpand
            , betaReduce
            , appProp
            , castPropagation
            , letRemoveSimple
            , letRec
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
