module CLaSH.Normalize.Strategy
  ( normalizeStrategy
  )
where

-- External Modules
import Language.KURE (Rewrite, repeatR, (.+), failR, extractR, (>->), (!->), bottomupR, topdownR, tryR, promoteR)

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Normalize.Types
import CLaSH.Normalize.Transformations
import CLaSH.Util.CoreHW (CoreContext, Term, TransformStep, transformationStep)

normalizeStrategy ::
  Rewrite NormalizeSession [CoreContext] Term
normalizeStrategy = keepTrying $ foldl1 (>->) $ map (extractR . bottomupR . tryR . promoteR . transformationStep) steps
  where
    steps = [ classopresolution
            , letFlat
            , letRemove
            , etaExpand
            , caseSimpl
            , retValSimpl
            , knownCase
            , scrutSimpl
            , funSpec
            , betaTyReduce
            , injectNonRepArguments
            , injectFunctionBindings
            , betaReduce
            , appProp
            , inlineNonRepResult
            , letRemoveUnused
            ]

keepTrying r = repeatR (r .+ failR "done")

specializePolymorphicValues ::
  Rewrite NormalizeSession [CoreContext] Term
specializePolymorphicValues = extractR $ foldl1 (>->) $ map (keepTrying . bottomupR . tryR . promoteR . transformationStep) steps
  where
    steps = [ funSpec
            , betaTyReduce
            ]

specializeFunctionValues ::
  Rewrite NormalizeSession [CoreContext] Term
specializeFunctionValues = extractR $ foldl1 (>->) $ map (bottomupR . tryR . promoteR . transformationStep) steps
  where
    steps = [ injectNonRepArguments
            , injectFunctionBindings
            ]

inlineNonReps ::
  Rewrite NormalizeSession [CoreContext] Term
inlineNonReps = extractR $ bottomupR $ tryR $ promoteR $ transformationStep inlineNonRepResult

cleanUp ::
  Rewrite NormalizeSession [CoreContext] Term
cleanUp = extractR $ foldl1 (>->) $ map (keepTrying . bottomupR . tryR . promoteR . transformationStep) steps
  where
    steps = [ letFlat
            , letRemove
            , classopresolution
            ]

betaNormal ::
  Rewrite NormalizeSession [CoreContext] Term
betaNormal = extractR $ foldl1 (>->) $ map (keepTrying . bottomupR . tryR . promoteR . transformationStep) steps
  where
    steps = [ betaReduce
            , appProp
            ]

misc ::
  Rewrite NormalizeSession [CoreContext] Term
misc = extractR $ foldl1 (>->) $ map (keepTrying . bottomupR . tryR . promoteR . transformationStep) steps
  where
    steps = [ etaExpand
            , caseSimpl
            , retValSimpl
            , knownCase
            , scrutSimpl
            , letRemoveUnused
            ]
