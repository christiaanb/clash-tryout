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

keepTrying r = repeatR (r .+ failR "done")
bottomupTry  = extractR . bottomupR . tryR . promoteR . transformationStep

normalizeStrategy = foldl1 (>->) steps
  where
    steps = [ reprStrategy
            , keepTrying ((bottomupTry classopresolution) !-> reprStrategy)
            , netlistStrategy
            ]

reprStrategy ::
  Rewrite NormalizeSession [CoreContext] Term
reprStrategy = keepTrying $ foldl1 (>->) $ map bottomupTry steps
  where
    steps = [ iotaReduce
            , betaReduce
            , caseApp
            , caseLet
            , caseLam
            , caseCon
            , caseCase
            , letApp
            , letLam
            , bindLam
            , bindBox
            , inlineBox
            , etaExpand
            , funcSpec
            , typeSpec
            ]

netlistStrategy ::
  Rewrite NormalizeSession [CoreContext] Term
netlistStrategy = keepTrying $ foldl1 (>->) $ map bottomupTry steps
  where
    steps = [ retLam
            , retLet
            , inlineVar
            , emptyLet
            , letFlat
            , deadCode
            , scrutSimpl
            , caseSimpl
            , caseRemove
            ]
