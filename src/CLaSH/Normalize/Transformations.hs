module CLaSH.Normalize.Transformations
  ( 
  -- * Cleanup transformations
  -- ** Beta-reduction
    betaReduce
  -- ** Unused Let Binding Removal  
  , letRemoveUnused
  -- ** Empty let removal
  , letRemove
  -- ** Simple Let Binding Removal
  , letRemoveSimple
  -- ** Cast Propagation
  , castPropagation
  -- ** Cast Simplification
  , castSimplification
  -- ** Top level binding inlining
  , inlineTopLevel
  -- * Program structure transformations
  -- ** Eta-expansion
  , etaExpand
  -- ** Application propagation
  , appProp
  -- ** Let recursification
  , letRec
  -- ** let flattening
  , letFlat
  -- ** Return value simplification
  , retValSimpl
  -- ** Representable arguments simplification
  , appSimpl
  -- ** Function Extraction
  , funExtract
  -- * Case normalization transformations
  -- ** Scrutinee simplification
  , scrutSimpl
  -- ** Scrutinee Binder Removal
  , scrutBndrRemove
  -- ** Case normalization
  , caseSimpl
  -- ** Case Removal
  , caseRemove
  -- ** Case of Known Constructor Simplification
  , knownCase
  -- * Unrepresentable value removal transformations
  -- ** Non-representable binding inlining
  , inlinenonrep
  -- ** Function Specialization
  , funSpec
  -- ** Non-representable result inlining
  , inlineNonRepResult
  )
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import Control.Monad.Trans (lift)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Label.PureM as Label
import Language.KURE (liftQ)

import Debug.Trace

-- GHC API
import qualified BasicTypes
import qualified Coercion
import qualified CoreFVs
import CoreSyn (Expr(..),Bind(..),AltCon(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified DataCon
import qualified Id
import qualified MkCore
import qualified Type
import qualified TysWiredIn
import qualified Var
import qualified VarSet

-- Internal Modules
import CLaSH.Driver.Tools (getGlobalExpr,addGlobalBind)
import {-# SOURCE #-} CLaSH.Normalize (normalizeMaybe)
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Util (curLoc)
import CLaSH.Util.Core ( CoreBinding, hasFreeTyVars, isApplicable, isVar
  , exprToVar, exprUsesBinders,isFun,isLam,isLet,viewVarOrApp,dataconIndex
  , TypedThing(..))
import CLaSH.Util.Core.Transform (regenUniques, changed, inlineBind
  , substitute, mkInternalVar, substituteAndClone)
import CLaSH.Util.Core.Types (CoreContext(..))
import CLaSH.Util.Pretty (pprString)

betaReduce :: NormalizeStep
betaReduce ctx (App (Lam bndr expr) arg) | Var.isTyVar bndr = substitute         bndr arg ctx expr >>= (changed ("beta: " ++ pprString arg ++ " " ++ pprString (getType arg)))
                                         | otherwise        = substituteAndClone bndr arg ctx expr >>= (changed ("beta: " ++ pprString arg ++ " " ++ pprString (getType arg)))

betaReduce ctx expr                                         = fail "beta"

letRemoveUnused :: NormalizeStep
letRemoveUnused ctx expr@(Let (Rec binds) res) = do
    let binds' = filter doBind binds
    if (length binds /= length binds')
      then
        changed "letRemoveUnused" (Let (Rec binds') res)
      else
        fail "letRemoveUnused"
  where
    boundExprs      = map snd binds
    doBind (bndr,_) = any (exprUsesBinders [bndr]) (res:boundExprs)

letRemoveUnused ctx expr = fail "letRemoveUnused"

-- | Remove empty (recursive) lets
letRemove :: NormalizeStep
letRemove ctx (Let (Rec []) res) = changed "letRemove" res

letRemove ctx expr               = fail "letRemove"

-- | Remove a = b bindings from let expressions everywhere
letRemoveSimple :: NormalizeStep
letRemoveSimple = inlineBind "letRemoveSimple" (\(b,e) -> isLocalVar e)

-- | Try to move casts as much downward as possible.
castPropagation :: NormalizeStep
castPropagation ctx (Cast (Let binds expr) ty)       = changed "castPropagation" $ Let binds (Cast expr ty)
castPropagation ctx (Cast (Case scrut b ty alts) co) = changed "castPropagation" $ Case scrut b (Coercion.applyCo ty co) alts'
  where
    alts' = map (\(con,bndrs,expr) -> (con,bndrs, Cast expr co)) alts
castPropagation ctx expr = fail "castPropagation"

-- | Mostly useful for state packing and unpacking, but
-- perhaps for others as well.
castSimplification :: NormalizeStep
castSimplification ctx expr@(Cast val ty) = do
  localVar <- liftQ $ isLocalVar val
  repr <- liftQ $ isRepr val
  if (not localVar) && repr
    then do
      castValId <- liftQ $ mkBinderFor val "castVal"
      changed "castSimplification" $ Let (Rec [(castValId,val)]) (Cast (Var castValId) ty)
    else
      fail "castSimplification"
      
castSimplification ctx expr = fail "castSimplification"

{- | 
This transformation inlines simple top level bindings. Simple
currently means that the body is only a single application (though
the complexity of the arguments is not currently checked) or that the
normalized form only contains a single binding. This should catch most of the
cases where a top level function is created that simply calls a type class
method with a type and dictionary argument, e.g.

@
  fromInteger = GHC.Num.fromInteger (SizedWord D8) $dNum
@

which is later called using simply

@
  fromInteger (smallInteger 10)
@

These useless wrappers are created by GHC automatically. If we don't
inline them, we get loads of useless components cluttering the
generated VHDL.

Note that the inlining could also inline simple functions defined by
the user, not just GHC generated functions. It turns out to be near
impossible to reliably determine what functions are generated and
what functions are user-defined. Instead of guessing (which will
inline less than we want) we will just inline all simple functions.

Only functions that are actually completely applied and bound by a
variable in a let expression are inlined. These are the expressions
that will eventually generate instantiations of trivial components.
By not inlining any other reference, we also prevent looping problems
with funextract and inlinedict.
-}
inlineTopLevel :: NormalizeStep
inlineTopLevel ctx@((LetBinding _):_) expr | not (isFun expr) =
  case (CoreSyn.collectArgs expr) of
    (Var f, args) -> do
      bodyMaybe <- liftQ $ needsInline f
      case bodyMaybe of
        Just body -> do
          bodyUniqued <- regenUniques ctx body
          changed "inlineTopLevel" (MkCore.mkCoreApps bodyUniqued args)
        Nothing -> fail "inlineTopLevel"
    _ -> fail "inlineTopLevel"

inlineTopLevel ctx expr = fail "inlineTopLevel"

needsInline :: CoreSyn.CoreBndr -> NormalizeSession (Maybe CoreSyn.CoreExpr)
needsInline bndr = do
  bodyMaybe <- (lift . lift) $ getGlobalExpr nsBindings bndr
  case bodyMaybe of
    Nothing -> return Nothing
    Just body -> case CoreSyn.collectArgs body of
      (Var f, args) -> return $ Just body
      _ -> do
        normMaybe <- normalizeMaybe False bndr
        case normMaybe of
          Nothing -> return Nothing
          Just (_,normExpr) -> case splitNormalizedNonRep normExpr of
            (args, [bind], Var res) -> return $ Just normExpr
            _ -> return Nothing

{- |
Make sure all parameters to the normalized functions are named by top
level lambda expressions. For this we apply η expansion to the
function body (possibly enclosed in some lambda abstractions) while
it has a function type. Eventually this will result in a function
body consisting of a bunch of nested lambdas containing a
non-function value (e.g., a complete application).
-}
etaExpand :: NormalizeStep
etaExpand (AppFirst:cs)  expr = fail "eta"

etaExpand (AppSecond:cs) expr = fail "eta"

etaExpand ctx expr | isFun expr && not (isLam expr) = do
  let argTy = (fst . Type.splitFunTy . getTypeFail) expr
  newId <- liftQ $ mkInternalVar "param" argTy
  changed "eta" (Lam newId (App expr (Var newId)))

etaExpand ctx expr = fail "eta"

-- | Move applications into let and case expressions.
appProp :: NormalizeStep
appProp ctx (App (Let binds expr) arg)        = changed "appProp" $ Let binds (App expr arg)

appProp ctx expr@(App (Case scrut b ty alts) arg)  = changed "appProp" $ Case scrut b ty' alts'
  where
    alts' = map (\(con,bndrs,expr) -> (con,bndrs, App expr arg)) alts
    ty'   = CoreUtils.applyTypeToArg ty arg
    
appProp ctx expr                              = fail "appProp"

-- | Make all lets recursive, so other transformations don't need to
-- handle non-recursive lets
letRec :: NormalizeStep
letRec ctx (Let (NonRec bndr val) res) = changed "letRec" $ Let (Rec [(bndr,val)]) res

letRec ctx expr                        = fail "letRec"

{- | 
Takes a let that binds another let, and turns that into two nested lets.
e.g., from:

@
let b = (let b' = expr' in res') in res
@

to:

@
let b' = expr' in (let b = res' in res)
@
-}
letFlat :: NormalizeStep
letFlat c topExpr@(Let (Rec binds) expr) = do
    let (binds',updated) = unzip $ map flatBind binds
    if (or updated) 
      then do
        changed "letFlat" $ Let (Rec $ concat binds') expr
      else
        fail "letFlat"
  where
    flatBind :: CoreBinding -> ([CoreBinding],Bool)
    flatBind (b, Let (Rec binds) expr) = ((b,expr):binds,True)
    flatBind (b, expr)                 = ([(b,expr)],False)

letFlat c expr = fail "letFlat"

{- |
Ensure the return value of a function follows proper normal form. eta
expansion ensures the body starts with lambda abstractions, this
transformation ensures that the lambda abstractions always contain a
recursive let and that, when the return value is representable, the
let contains a local variable reference in its body.
-}
retValSimpl :: NormalizeStep
retValSimpl ctx expr | all isLambdaBodyCtx ctx && not (isLam expr) && not (isLet expr) = do
  localVar <- liftQ $ isLocalVar expr
  repr <- liftQ $ isRepr expr
  if not localVar && repr
    then do
      resId <- liftQ $ mkBinderFor expr "res"
      changed "retValSimpl" $ Let (Rec [(resId, expr)]) (Var resId)
    else
      fail "retValSimpl"

retValSimpl ctx expr@(Let (Rec binds) body) | all isLambdaBodyCtx ctx = do
  localVar <- liftQ $ isLocalVar body
  repr <- liftQ $ isRepr body
  if not localVar && repr
    then do
      resId <- liftQ $ mkBinderFor body "res"
      changed "retValSimpl" $ Let (Rec $ (resId,body):binds) (Var resId)
    else
      fail "retValSimpl"

retValSimpl ctx expr = fail "retValSimpl"

-- | Make sure that all arguments of a representable type are simple variables.
appSimpl :: NormalizeStep
appSimpl ctx expr@(App f arg) = do
  repr <- liftQ $ isRepr arg
  localVar <- liftQ $ isLocalVar arg
  if repr && not localVar
    then do
      argId <- liftQ $ mkBinderFor arg "arg"
      changed "appSimpl" $ Let (Rec [(argId,arg)]) (App f (Var argId))
    else
      fail "appSimpl"

appSimpl ctx expr = fail "appSimpl"

{- | 
This transform takes any function-typed argument that cannot be propagated
(because the function that is applied to it is a builtin function), and
puts it in a brand new top level binder. This allows us to for example
apply map to a lambda expression This will not conflict with inlinenonrep,
since that only inlines local let bindings, not top level bindings.
-}
funExtract :: NormalizeStep
funExtract ctx expr@(App _ _) | isVar fexpr = do
    bodyMaybe <- liftQ $ (lift . lift) $ getGlobalExpr nsBindings f
    case bodyMaybe of
      Nothing -> do
        args' <- liftQ $ mapM doArg args
        if or (map fst args') 
          then
            changed "funExtract" $ MkCore.mkCoreApps fexpr (map snd args')
          else
            fail "funExtract"
      Just _ -> fail "funExtract"
  where
    (fexpr, args) = CoreSyn.collectArgs expr
    Var f         = fexpr
    
    doArg arg | not (viewVarOrApp arg) && isApplicable arg && not (hasFreeTyVars arg) = do
      let freeVars = VarSet.varSetElems $ CoreFVs.exprFreeVars arg
      let body     = MkCore.mkCoreLams freeVars arg
      funId <- mkBinderFor body "fun"
      (lift . lift) $ addGlobalBind nsBindings funId body
      return $ (True, MkCore.mkCoreApps (Var funId) (map Var freeVars))
    doArg arg = return (False, arg)

funExtract ctx expr = fail "funExtract"

-- | Make sure the scrutinee of a case expression is a local variable
-- reference.
scrutSimpl :: NormalizeStep
scrutSimpl c expr@(Case scrut b ty alts) = do
  repr <- liftQ $ isRepr scrut
  localVar <- liftQ $ isLocalVar scrut
  if repr && not localVar
    then do
      scrutId <- liftQ $ mkBinderFor scrut "scrut"
      changed "scrutSimpl" $ Let (Rec [(scrutId,scrut)]) (Case (Var scrutId) b ty alts)
    else
      fail "scrutSimpl"

scrutSimpl ctx expr = fail "scrutSimpl"

{- |
A case expression can have an extra binder, to which the scrutinee is bound
after bringing it to WHNF. This is used for forcing evaluation of strict
arguments. Since strictness does not matter for us (rather, everything is
sort of strict), this binder is ignored when generating VHDL, and must thus
be wild in the normal form.
-}
scrutBndrRemove :: NormalizeStep
scrutBndrRemove ctx (Case (Var scrut) bndr ty alts) | bndrUsed = do
    alts' <- mapM substBndrAlt alts
    changed "scrutBndrRemove" $ Case (Var scrut) wild ty alts'
  where
    isUsed (_,_,expr) = exprUsesBinders [bndr] expr
    bndrUsed          = or $ map isUsed alts
    substBndrAlt (con,bndrs,expr) = do
      expr' <- substitute bndr (Var scrut) ctx expr
      return (con, bndrs, expr')
    wild = MkCore.mkWildValBinder (Id.idType bndr)

scrutBndrRemove ctx expr = fail "scrutBndrRemove"

{- |
Turn a case expression with any number of alternatives with any
number of non-wild binders into as set of case and let expressions,
all of which are in normal form (e.g., a bunch of extractor case
expressions to extract all fields from the scrutinee, a number of let
bindings to bind each alternative and a single selector case to
select the right value.
-}
caseSimpl :: NormalizeStep
caseSimpl ctx expr@(Case scrut b ty [(cont, bndrs, Var x)]) = fail "caseSimpl"

caseSimpl ctx topExpr@(Case scrut bndr ty alts) | not bndrUsed = do
    (bindingss, alts') <- liftQ $ fmap unzip $ mapM doAlt alts
    let bindings = concat bindingss
    let newLet   = MkCore.mkCoreLet (Rec bindings) (Case scrut bndr ty alts')
    if null bindings
      then fail "caseSimpl"
      else changed "caseSimpl" newLet
  where
    isUsed (_,_,expr) = exprUsesBinders [bndr] expr
    bndrUsed = or $ map isUsed alts
    
    doAlt :: CoreSyn.CoreAlt -> NormalizeSession ([CoreBinding], CoreSyn.CoreAlt)
    doAlt (LitAlt _, _, _) = Error.throwError $ $(curLoc) ++ "Don't know how to handle LitAlt in case expression: " ++ show topExpr
    
    doAlt alt@(DEFAULT, [], expr) = do
      localVar <- isLocalVar expr
      repr <- isRepr expr
      (exprBindingMaybe, expr') <- if (not localVar) && repr
        then do
          caseValId <- mkBinderFor expr "caseVal"
          return (Just (caseValId,expr), Var caseValId)
        else
          return (Nothing, expr)
      let newAlt = (DEFAULT, [], expr')
      let bindings = Maybe.catMaybes [exprBindingMaybe]
      return (bindings, newAlt)
      
    doAlt (DataAlt dc, bndrs, expr) = do
        bndrsRes <- Monad.zipWithM doBndr bndrs [0..]
        let (newBndrs, bindingsMaybe) = unzip bndrsRes
        let usesBndrs = not $ VarSet.isEmptyVarSet $ CoreFVs.exprSomeFreeVars (`elem` newBndrs) expr
        (exprBindingMaybe, expr') <- doExpr expr usesBndrs
        let newAlt = (DataAlt dc, newBndrs, expr')
        let bindings = Maybe.catMaybes (bindingsMaybe ++ [exprBindingMaybe])
        return (bindings, newAlt)
      where
        wildBndrs = map (MkCore.mkWildValBinder . Id.idType) bndrs
        freeVars  = CoreFVs.exprSomeFreeVars (`elem` bndrs) expr
        doBndr :: CoreSyn.CoreBndr -> Int -> NormalizeSession (CoreSyn.CoreBndr, Maybe CoreBinding)
        doBndr b i = do
          repr <- isRepr b
          let wild = not (VarSet.elemVarSet b freeVars)
          if (not wild) && repr
            then do
              dcI <- dataconIndex (getTypeFail scrut) dc
              caseExpr <- mkSelCase scrut dcI i
              return (wildBndrs!!i, Just (b,caseExpr))
            else
              return (b,Nothing)
        doExpr :: CoreSyn.CoreExpr -> Bool -> NormalizeSession (Maybe CoreBinding, CoreSyn.CoreExpr)
        doExpr expr usesBndrs = do
          localVar <- isLocalVar expr
          repr <- isRepr expr
          if (not usesBndrs) && (not localVar) && repr
            then do
              caseValId <- mkBinderFor expr "caseVal"
              return (Just (caseValId, expr), Var caseValId)
            else
              return (Nothing, expr)
              
caseSimpl ctx expr = fail "caseSimpl"

-- | Remove case statements that have only a single alternative and only wild
-- binders.
caseRemove :: NormalizeStep
caseRemove ctx (Case scrut b ty [(con,bndrs,expr)]) | not usesVars = changed "caseRemove" expr
  where
    usesVars = exprUsesBinders (b:bndrs) expr
caseRemove ctx expr = fail "caseRemove"

{- |
If a case expressions scrutinizes a datacon application, we can
determine which alternative to use and remove the case alltogether.
We replace it with a let expression the binds every binder in the
alternative bound to the corresponding argument of the datacon. We do
this instead of substituting the binders, to prevent duplication of
work and preserve sharing wherever appropriate.
-}
knownCase :: NormalizeStep
knownCase ctx expr@(Case scrut@(App _ _) bndr ty alts) | not bndrUsed = do
    case CoreSyn.collectArgs scrut of
      (Var f, args) -> case Id.isDataConId_maybe f of
        Nothing -> fail "knownCase"
        Just dc -> do
          let (altcon,bndrs,res) = case List.find (\(altcon,bndr,res) -> altcon == (DataAlt dc)) alts of
                Just alt -> alt
                Nothing  -> head alts
          if altcon /= (DataAlt dc) && altcon /= DEFAULT
            then do
              liftQ $ Error.throwError $ $(curLoc) ++ "Invalid core, datacon not found in alternatie and DEFAULT alternative is not first?\n" ++ pprString expr
            else do
              let (tvs, preds, _, _) = DataCon.dataConSig dc
              let count = length tvs + length preds
              let binds = zip bndrs (drop count args)
              changed "knownCase" $ Let (Rec binds) res
  where
    isUsed (_, _, expr) = exprUsesBinders [bndr] expr
    bndrUsed            = or $ map isUsed alts

knownCase ctx expr = fail "knownCase"

{- |
Remove a = B bindings, with B of a non-representable type, from let
expressions everywhere. This means that any value that we can't generate a
signal for, will be inlined and hopefully turned into something we can
represent.

This is a tricky function, which is prone to create loops in the
transformations. To fix this, we make sure that no transformation will
create a new let binding with a non-representable type. These other
transformations will just not work on those function-typed values at first,
but the other transformations (in particular β-reduction) should make sure
that the type of those values eventually becomes representable.
-}
inlinenonrep :: NormalizeStep
inlinenonrep ctx expr = inlineBind ("inlinenonrep: " ++ pprString expr) (fmap not . isRepr . snd) ctx expr

{- |
Remove all applications to non-representable arguments, by duplicating the
function called with the non-representable parameter replaced by the free
variables of the argument passed in.
-}
funSpec :: NormalizeStep
funSpec ctx expr@(App _ _) | isVar fexpr = do
    bodyMaybe <- liftQ $ (lift . lift) $ getGlobalExpr nsBindings f
    case bodyMaybe of
      Just body -> do
        (args',updated) <- fmap unzip $ liftQ $ mapM doArg args
        case (or updated) of
          True -> do
            let (newArgs',newParams',oldArgs) = unzip3 args'
            let newArgs   = concat newArgs'
            let newParams = concat newParams'
            let newBody   = MkCore.mkCoreLams newParams (MkCore.mkCoreApps body oldArgs)
            newf <- liftQ $ mkFunction f newBody
            let newExpr = MkCore.mkCoreApps (Var newf) newArgs
            changed "funSpec" newExpr
          False ->
            fail "funSpec"
      Nothing -> fail "funSpec"
  where
    (fexpr,args) = CoreSyn.collectArgs expr
    (Var f)      = fexpr
    
    doArg :: CoreSyn.CoreExpr -> NormalizeSession (([CoreSyn.CoreExpr], [CoreSyn.CoreBndr], CoreSyn.CoreExpr), Bool)
    doArg arg = do
      repr <- isRepr arg
      bndrs <- fmap (Map.keys) $ (lift . lift) $ Label.gets nsBindings
      let interesting var = Var.isLocalVar var && (var `notElem` bndrs)
      if (not repr) && (not (isVar arg && interesting (exprToVar arg))) && (not (hasFreeTyVars arg))
        then do
          let freeVars = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars interesting arg
          return ((map Var freeVars, freeVars, arg),True)
        else do
          paramId <- mkBinderFor arg "param"
          return (([arg],[paramId], mkReferenceTo paramId),False)

funSpec ctx expr = fail "funSpec"

{- |
This transformation takes a function (top level binding) that has a
non-representable result (e.g., a tuple containing a function, or an
Integer. The latter can occur in some cases as the result of the
fromIntegerT function) and inlines enough of the function to make the
result representable again.

This is done by first normalizing the function and then \"inlining\"
the result. Since no unrepresentable let bindings are allowed in
normal form, we can be sure that all free variables of the result
expression will be representable (Note that we probably can't
guarantee that all representable parts of the expression will be free
variables, so we might inline more than strictly needed).

The new function result will be a tuple containing all free variables
of the old result, so the old result can be rebuild at the caller.

We take care not to inline dictionary id's, which are top level
bindings with a non-representable result type as well, since those
will never become VHDL signals directly. There is a separate
transformation (inlinedict) that specifically inlines dictionaries
only when it is useful.
-}
inlineNonRepResult :: NormalizeStep
inlineNonRepResult ctx expr | not (isApplicable expr) && not (hasFreeTyVars expr) = do
  case CoreSyn.collectArgs expr of
    (Var f, args) | not (Id.isDictId f || Id.isDFunId f) -> do
      repr <- liftQ $ isRepr expr
      if not repr
        then do
          bodyMaybe <- liftQ $ normalizeMaybe True f
          case bodyMaybe of
            Just body -> do
              let (bndrs,binds,res) = splitNormalizedNonRep $ snd body
              if hasFreeTyVars res
                then
                  fail "inlineNonRepResult"
                else do
                  globalBndrs <- fmap (Map.keys) $ liftQ $ (lift . lift) $ Label.gets nsBindings
                  let interesting var = Var.isLocalVar var && (var `notElem` globalBndrs)
                  let freeVars = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars interesting res
                  let freeVarTypes = map Id.idType freeVars
                  let cntFreeVars = length freeVars
                  let fvsDatacon = TysWiredIn.tupleCon BasicTypes.Boxed cntFreeVars
                  let fvsDataconId = DataCon.dataConWorkId fvsDatacon
                  let newRes = if (cntFreeVars == 1) then res else MkCore.mkCoreApps (Var fvsDataconId) (map Type freeVarTypes ++ map Var freeVars)
                  let newBody = CoreSyn.mkLams bndrs (Let (Rec binds) newRes)
                  f' <- liftQ $ mkFunction f newBody
                  let newApp = MkCore.mkCoreApps (Var f') args
                  resBndr <- liftQ $ mkBinderFor newApp "res"
                  selCases <- liftQ $ if (cntFreeVars == 1) then
                      return [(Var resBndr)]
                    else
                      mapM (mkSelCase (Var resBndr) 0) [0..cntFreeVars-1]
                  let binds = (resBndr,newApp):(zip freeVars selCases)
                  let letExpr = Let (Rec binds) res
                  letExprUniqued <- regenUniques ctx letExpr
                  changed "inlineNonRepResult" letExprUniqued
            Nothing -> fail "inlineNonRepResult"
        else
          fail "inlineNonRepResult"
    _ -> fail "inlineNonRepResult"

inlineNonRepResult c expr = fail "inlineNonRepResult"
