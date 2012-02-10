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
            --, keepTrying ((bottomupTry classopresolution) !-> reprStrategy)
            , simplifyStrategy
            ]

reprStrategy ::
  Rewrite NormalizeSession [CoreContext] Term
reprStrategy = keepTrying $ foldl1 (>->) steps
  where
    steps = [ typePropStrategy
            , firstOrderStrategy
            ]

typePropStrategy ::
  Rewrite NormalizeSession [CoreContext] Term
typePropStrategy = keepTrying $ foldl1 (>->) $ map bottomupTry steps
  where
    steps = [ lamApp
            , letApp
            , caseApp
            , iotaReduce
            , letTyApp
            , caseTyApp
            , bindPoly
            , typeSpec
            ]

firstOrderStrategy ::
  Rewrite NormalizeSession [CoreContext] Term
firstOrderStrategy = keepTrying $ foldl1 (>->) $ map bottomupTry steps
  where
    steps = [ lamApp
            , letApp
            , caseApp
            , caseLet
            , caseCon
            , caseCase
            , inlineBox
            , bindFun
            , funSpec
            ]

simplifyStrategy ::
  Rewrite NormalizeSession [CoreContext] Term
simplifyStrategy = keepTrying $ foldl1 (>->) $ map bottomupTry steps
  where
    steps = [ lamApp
            , letApp
            , caseApp
            , deadCode
            , bindNonRep
            , nonRepSpec
            , inlineNonRep
            , funcLift
            , etaExpand
            , appSimpl
            , retLam
            , retLet
            , letFlat
            , inlineVar
            , letLam
            , caseLam
            , scrutSimpl
            , caseRemove
            , caseSimpl
            ]
