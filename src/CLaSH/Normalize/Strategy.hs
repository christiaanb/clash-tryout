module CLaSH.Normalize.Strategy
  ( arrowDesugarStrategy
  , normalizeStrategy
  , startContext
  )
where

-- External Modules
import Language.KURE

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Normalize.Traverse
import CLaSH.Normalize.Transformations

startContext :: [CoreContext]
startContext = []

arrowDesugarStrategy :: Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
arrowDesugarStrategy = repeatR (arrowDesugarStrategy' .+ failR "done")

arrowDesugarStrategy' :: Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
arrowDesugarStrategy' = extractR $ topdownR $ foldl1 (>->) $ map (tryR . promoteR . transformationStep) steps
  where
    steps = [ inlineArrowBndr            
            , arrowComponentDesugar
            , arrowArrDesugar
            , arrowReturnADesugar
            , arrowHooksDesugar
            , arrowFirstDesugar
            ]

normalizeStrategy :: Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
normalizeStrategy = repeatR (normalizeStrategy' .+ failR "done")

normalizeStrategy' :: Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
normalizeStrategy' = extractR $ bottomupR $ foldl1 (>->) $ map (tryR . promoteR . transformationStep) steps
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
