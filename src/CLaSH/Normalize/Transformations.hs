{-# LANGUAGE PatternGuards #-}
module CLaSH.Normalize.Transformations
  (
  -- * Cleanup transformations
  -- ** Beta-reduction
    betaReduce
  , betaTyReduce
  -- ** Unused Let Binding Removal
  , letRemoveUnused
  -- ** Empty let removal
  , letRemove
  ---- ** Simple Let Binding Removal
  --, letRemoveSimple
  ---- ** Top level binding inlining
  --, inlineTopLevel
  -- * Program structure transformations
  -- ** Eta-expansion
  , etaExpand
  -- ** Application propagation
  , appProp
  -- ** let flattening
  , letFlat
  -- ** Return value simplification
  , retValSimpl
  ---- ** Function Extraction
  --, funExtract
  -- * Case normalization transformations
  -- ** Scrutinee simplification
  , scrutSimpl
  ---- ** Scrutinee Binder Removal
  --, scrutBndrRemove
  -- ** Case normalization
  , caseSimpl
  ---- ** Case Removal
  --, caseRemove
  -- ** Case of Known Constructor Simplification
  , knownCase
  ---- * Unrepresentable value removal transformations
  -- ** Function binding injection
  , injectFunctionBindings
  -- ** Function Specialization
  , funSpec
  -- ** Nonrep argument injection
  , injectNonRepArguments
  ---- ** Non-representable result inlining
  , inlineNonRepResult
  , classopresolution
  )
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import Control.Monad.Trans (lift)
import qualified Data.Either as Either
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Label.PureM as Label
import Language.KURE (RewriteM, liftQ, runRewrite, extractR, bottomupR, tryR, promoteR)

-- GHC API
import qualified BasicTypes
import qualified DataCon
import qualified Class
import qualified Id
import qualified MkCore
import qualified TyCon
import qualified Type
import qualified TysWiredIn
import qualified Var
import qualified VarSet

-- Internal Modules
import CLaSH.Netlist.Constants        (builtinIds)
import {-# SOURCE #-} CLaSH.Normalize (normalizeMaybe)
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Util (curLoc, partitionM, secondM)
import CLaSH.Util.CoreHW (CoreContext(..), Term(..), AltCon(..), TypedThing(..), Var, CoreBinding, Type, changed, mkInternalVar, isFun, isLam, applyFunTy, substituteType, substituteVar, termString, termSomeFreeVars, exprUsesBinders, dataConIndex, isLet, collectArgs, isPoly, tyHasFreeTyVars, mkApps, mkLams, isApplicable, transformationStep, startContext, varString, hasFreeTyVars, isVar, varStringUniq,termFreeVars, regenUniques)
import CLaSH.Util.Pretty (pprString)

betaReduce :: NormalizeStep
betaReduce ctx e@(App (Lambda bndr expr) arg) = substituteVar bndr arg ctx expr >>= (changed "beta" e)
betaReduce ctx expr                         = fail "beta"

betaTyReduce :: NormalizeStep
betaTyReduce ctx e@(TyApp (TyLambda tv expr) t) = substituteType tv t ctx expr    >>= (changed "betaTY" e)
betaTyReduce ctx expr                         = fail "betaTy"

letRemoveUnused :: NormalizeStep
letRemoveUnused ctx expr@(LetRec binds res) = do
    let binds' = filter doBind binds
    if (length binds /= length binds')
      then
        changed "letRemoveUnused" expr (LetRec binds' res)
      else
        fail "letRemoveUnused"
  where
    boundExprs      = map snd binds
    doBind (bndr,_) = any (exprUsesBinders [bndr]) (res:boundExprs)

letRemoveUnused ctx expr = fail "letRemoveUnused"

-- | Remove empty (recursive) lets
letRemove :: NormalizeStep
letRemove ctx e@(LetRec [] res) = changed "letRemove" e res

letRemove ctx expr            = fail "letRemove"

---- | Remove a = b bindings from let expressions everywhere
--letRemoveSimple :: NormalizeStep
--letRemoveSimple = inlineBind "letRemoveSimple" (\(b,e) -> isLocalVar e)

--{- |
--This transformation inlines simple top level bindings. Simple
--currently means that the body is only a single application (though
--the complexity of the arguments is not currently checked) or that the
--normalized form only contains a single binding. This should catch most of the
--cases where a top level function is created that simply calls a type class
--method with a type and dictionary argument, e.g.

-- @
--  fromInteger = GHC.Num.fromInteger (SizedWord D8) $dNum
-- @

--which is later called using simply

-- @
--  fromInteger (smallInteger 10)
-- @

--These useless wrappers are created by GHC automatically. If we don't
--inline them, we get loads of useless components cluttering the
--generated VHDL.

--Note that the inlining could also inline simple functions defined by
--the user, not just GHC generated functions. It turns out to be near
--impossible to reliably determine what functions are generated and
--what functions are user-defined. Instead of guessing (which will
--inline less than we want) we will just inline all simple functions.

--Only functions that are actually completely applied and bound by a
--variable in a let expression are inlined. These are the expressions
--that will eventually generate instantiations of trivial components.
--By not inlining any other reference, we also prevent looping problems
--with funextract and inlinedict.
---}
--inlineTopLevel :: NormalizeStep
--inlineTopLevel ctx@((LetBinding _):_) expr | not (isFun expr) =
--  case (CoreSyn.collectArgs expr) of
--    (Var f, args) -> do
--      bodyMaybe <- liftQ $ needsInline f
--      case bodyMaybe of
--        Just body -> do
--          bodyUniqued <- regenUniques ctx body
--          changed "inlineTopLevel" (MkCore.mkCoreApps bodyUniqued args)
--        Nothing -> fail "inlineTopLevel"
--    _ -> fail "inlineTopLevel"

--inlineTopLevel ctx expr = fail "inlineTopLevel"

--needsInline :: CoreSyn.CoreBndr -> NormalizeSession (Maybe CoreSyn.CoreExpr)
--needsInline bndr = do
--  bodyMaybe <- (lift . lift) $ getGlobalExpr nsBindings bndr
--  case bodyMaybe of
--    Nothing -> return Nothing
--    Just body -> case CoreSyn.collectArgs body of
--      (Var f, args) -> return $ Just body
--      _ -> do
--        normMaybe <- normalizeMaybe False bndr
--        case normMaybe of
--          Nothing -> return Nothing
--          Just (_,normExpr) -> case splitNormalizedNonRep normExpr of
--            (args, [bind], Var res) -> return $ Just normExpr
--            _ -> return Nothing

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

etaExpand ctx expr | isFun expr && not (isLam expr) = do
  let argTy = (fst . Maybe.fromMaybe (error "etaExpand splitFunTy") . Type.splitFunTy_maybe . getTypeFail) expr
  newId <- liftQ $ mkInternalVar "p" argTy
  changed "eta" expr (Lambda newId (App expr newId))

etaExpand ctx expr = fail "eta"

-- | Move applications into let and case expressions.
appProp :: NormalizeStep
appProp ctx e@(App (LetRec binds expr) arg)      = changed "appProp" e $ LetRec binds (App expr arg)

appProp ctx expr@(App (Case scrut ty alts) arg)  = changed "appProp" expr $ Case scrut ty' alts'
  where
    alts' = map (\(con,expr') -> (con, App expr' arg)) alts
    ty'   = applyFunTy ty (Id.idType arg)

appProp ctx expr                                   = fail "appProp"

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
letFlat c topExpr@(LetRec binds expr) = do
    let (binds',updated) = unzip $ map flatBind binds
    if (or updated)
      then do
        changed "letFlat" topExpr $ LetRec  (concat binds') expr
      else
        fail "letFlat"
  where
    flatBind :: CoreBinding -> ([CoreBinding],Bool)
    flatBind (b, LetRec binds expr) = ((b,expr):binds,True)
    flatBind (b, expr)              = ([(b,expr)],False)

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
      changed "retValSimpl" expr $ LetRec [(resId, expr)] (Var resId)
    else
      fail "retValSimpl"

retValSimpl ctx expr@(LetRec binds body) | all isLambdaBodyCtx ctx = do
  localVar <- liftQ $ isLocalVar body
  repr <- liftQ $ isRepr body
  if not localVar && repr
    then do
      resId <- liftQ $ mkBinderFor body "res"
      changed "retValSimpl" expr $ LetRec ((resId,body):binds) (Var resId)
    else
      fail "retValSimpl"

retValSimpl [] e@(Lambda x (Var y)) | x == y = do
  resId <- liftQ $ mkBinderFor (Var y) "res"
  changed "retValSimpl" e $ Lambda x $ LetRec [(resId,Var y)] (Var resId)

retValSimpl ctx expr = fail "retValSimpl"

-- | Make sure the scrutinee of a case expression is a local variable
-- reference.
scrutSimpl :: NormalizeStep
scrutSimpl c expr@(Case scrut ty alts) = do
  repr <- liftQ $ isRepr scrut
  localVar <- liftQ $ isLocalVar scrut
  if repr && not localVar
    then do
      scrutId <- liftQ $ mkBinderFor scrut "scrut"
      changed "scrutSimpl" expr $ LetRec [(scrutId,scrut)] (Case (Var scrutId) ty alts)
    else
      fail "scrutSimpl"

scrutSimpl ctx expr = fail "scrutSimpl"

{- |
Turn a case expression with any number of alternatives with any
number of non-wild binders into as set of case and let expressions,
all of which are in normal form (e.g., a bunch of extractor case
expressions to extract all fields from the scrutinee, a number of let
bindings to bind each alternative and a single selector case to
select the right value.
-}
caseSimpl :: NormalizeStep
caseSimpl ctx expr@(Case scrut ty [(cont, Var x)]) = fail "caseSimpl"

caseSimpl ctx topExpr@(Case scrut ty alts) = do
    (bindingss, alts') <- liftQ $ fmap unzip $ mapM doAlt alts
    let bindings = concat bindingss
    let newLet   = LetRec bindings (Case scrut ty alts')
    if null bindings
      then fail "caseSimpl"
      else changed "caseSimpl" topExpr newLet
  where
    doAlt :: (AltCon, Term) -> NormalizeSession ([CoreBinding], (AltCon, Term))
    doAlt (LiteralAlt _, _) = Error.throwError $ $(curLoc) ++ "Don't know how to handle LitAlt in case expression: " ++ show topExpr

    doAlt alt@(DefaultAlt, expr) = do
      localVar <- isLocalVar expr
      repr <- isRepr expr
      (exprBindingMaybe, expr') <- if (not localVar) && repr
        then do
          caseValId <- mkBinderFor expr "caseAlt"
          return (Just (caseValId,expr), Var caseValId)
        else
          return (Nothing, expr)
      let newAlt = (DefaultAlt, expr')
      let bindings = Maybe.catMaybes [exprBindingMaybe]
      return (bindings, newAlt)

    doAlt (DataAlt dc tyBndrs varBndrs, expr) = do
        bndrsRes <- Monad.zipWithM doBndr varBndrs [0..]
        let (newBndrs, bindingsMaybe) = unzip bndrsRes
        let usesBndrs = not $ VarSet.isEmptyVarSet $ termSomeFreeVars (`elem` newBndrs) expr
        (exprBindingMaybe, expr') <- doExpr expr usesBndrs
        let newAlt = (DataAlt dc tyBndrs newBndrs, expr')
        let bindings = Maybe.catMaybes (bindingsMaybe ++ [exprBindingMaybe])
        return (bindings, newAlt)
      where
        wildBndrs = map (MkCore.mkWildValBinder . Id.idType) varBndrs
        freeVars  = termSomeFreeVars (`elem` varBndrs) expr
        doBndr :: Var -> Int -> NormalizeSession (Var, Maybe CoreBinding)
        doBndr b i = do
          repr <- isRepr b
          let wild = not (VarSet.elemVarSet b freeVars)
          if (not wild) && repr
            then do
              dcI <- dataConIndex (getTypeFail scrut) dc
              caseExpr <- mkSelCase "caseSimpl" scrut dcI i
              return (wildBndrs!!i, Just (b,caseExpr))
            else
              return (b,Nothing)
        doExpr :: Term -> Bool -> NormalizeSession (Maybe CoreBinding, Term)
        doExpr expr usesBndrs = do
          localVar <- isLocalVar expr
          repr <- isRepr expr
          if (not usesBndrs) && (not localVar) && repr
            then do
              caseValId <- mkBinderFor expr "caseAlt"
              return (Just (caseValId, expr), Var caseValId)
            else
              return (Nothing, expr)

caseSimpl ctx expr = fail "caseSimpl"

---- | Remove case statements that have only a single alternative and only wild
---- binders.
--caseRemove :: NormalizeStep
--caseRemove ctx (Case scrut b ty [(con,bndrs,expr)]) | not usesVars = changed "caseRemove" expr
--  where
--    usesVars = exprUsesBinders (b:bndrs) expr
--caseRemove ctx expr = fail "caseRemove"

{- |
If a case expressions scrutinizes a datacon application, we can
determine which alternative to use and remove the case alltogether.
We replace it with a let expression the binds every binder in the
alternative bound to the corresponding argument of the datacon. We do
this instead of substituting the binders, to prevent duplication of
work and preserve sharing wherever appropriate.
-}
knownCase :: NormalizeStep
knownCase ctx expr@(Case scrut@(Data dc as xs) ty alts) = do
  let (altcon, res) = case List.find
                          (\(altcon', _) -> case altcon' of
                            DataAlt dc' _ _ -> dc == dc'
                            _ -> False
                          ) alts of
                        Just alt -> alt
                        Nothing  -> head alts
  case altcon of
    DefaultAlt      -> do
      changed "knownCase" expr res
    DataAlt _ _ xs' -> do
      let binds = zip xs' (map Var xs)
      changed "knownCase" expr $ LetRec binds res
    _ -> liftQ $ Error.throwError $ $(curLoc) ++ "Invalid core, datacon not found in alternative and DEFAULT alternative not first?"

knownCase ctx expr@(Case scrut@(LetRec binds (Data dc as xs)) ty alts) = do
  let (altcon, res) = case List.find
                          (\(altcon', _) -> case altcon' of
                            DataAlt dc' _ _ -> dc == dc'
                            _ -> False
                          ) alts of
                        Just alt -> alt
                        Nothing  -> head alts
  case altcon of
    DefaultAlt      -> do
      changed "knownCase" expr res
    DataAlt _ _ xs' -> do
      let binds' = zip xs' (map Var xs)
      changed "knownCase" expr $ LetRec (binds' ++ binds) res
    _ -> liftQ $ Error.throwError $ $(curLoc) ++ "Invalid core, datacon not found in alternative and DEFAULT alternative not first?"

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
injectFunctionBindings :: NormalizeStep
injectFunctionBindings ctx e@(LetRec binds res) = do
  let (injectableM,others)  = List.partition (isFun . snd) $ binds
  let (inArgPos,injectable) = List.partition (fst) $ map (\(b,e) -> (or $ map (varInArgPosition b . snd) binds ++ [varInArgPosition b res], (b,e))) injectableM
  case injectable of
    [] -> fail "injectFunctionBindings"
    _  -> do
      newExpr <- liftQ $ injectBinding (map snd injectable) (LetRec (map snd inArgPos ++ others) res)
      changed ("injectFunctionBindings")  e newExpr

injectFunctionBindings _ _ = fail "injectFunctionBindings"

injectBinding ::
  [(Var,Term)]
  -> Term
  -> NormalizeSession Term
injectBinding [] expr = return expr
injectBinding ((bndr,val):reps) expr = do
  expr' <- injectExpr bndr val expr
  reps' <- mapM (secondM $ injectExpr bndr val) reps
  injectBinding reps' expr'

injectExpr ::
  Var
  -> Term
  -> Term
  -> NormalizeSession Term
injectExpr find repl expr = do
  rwRes <- runRewrite ((extractR . bottomupR . tryR . promoteR . transformationStep) injectExpr') startContext expr
  expr' <- case rwRes of
      Right (rwExpr,_,_) -> return rwExpr
      Left errMsg        -> Error.throwError $ $(curLoc) ++ "injectExpr failed: " ++ errMsg
  return expr'
  where
    injectExpr' context expr@(Var var)       | find == var = return repl
    injectExpr' context expr@(App e var)
      | find == var
      , (Var f, args) <- collectArgs e
      = do
        bodyMaybe <- liftQ $ getGlobalExpr f
        case bodyMaybe of
          Just body -> do
            bndrs <- fmap (Map.keys) $ (liftQ . lift . lift) $ Label.gets nsBindings
            let interesting var = Var.isLocalVar var && (var `notElem` bndrs)
            let freeVars = VarSet.varSetElems $ termSomeFreeVars interesting repl
            argParams <- liftQ $ mapM
                            (\v -> case v of
                                Left a  -> mkBinderFor a "paramArg"
                                Right t -> mkTyBinderFor t "paramType"
                            ) args
            ebndr     <- liftQ $ mkBinderFor repl "inlineF"
            let newArgs = map (\v -> if Var.isTyVar v then Right (Type.mkTyVarTy v) else Left v) argParams
            repl'   <- liftQ $ regenUniques repl
            let newBody = mkLams (argParams ++ freeVars) (LetRec [(ebndr,repl')] (mkApps body (newArgs ++ [Left ebndr])))
            newf <- liftQ $ mkFunction f newBody
            let newExpr = mkApps (Var newf) $ args ++ (map Left freeVars)
            return newExpr
          Nothing -> fail "injectExpr'"
      | find == var
      , (_, args) <- collectArgs e
      = liftQ $ Error.throwError $ $(curLoc) ++ "Not in eta-beta normal form: " ++ pprString expr

    injectExpr' context expr                           = fail "injectExpr'"

{- |
Function specialization duplicates a function called with type arguments,
and passes in the type arguments. At the call site, the new function, without
type arguments, will be placed.
-}
funSpec :: NormalizeStep
funSpec ctx expr@(App _ _)
  | (Var f, args) <- collectArgs expr
  , not (isPoly expr)
  , not $ null (Either.rights args)
  = funSpec' f args ctx expr
funSpec ctx expr@(TyApp _ _)
  | (Var f, args) <- collectArgs expr
  , not (isPoly expr)
  , not $ null (Either.rights args)
  = funSpec' f args ctx expr

funSpec _   _ = fail "funSpec"

funSpec' ::
  Var
  -> [Either Var Type]
  -> NormalizeStep
funSpec' f args _ e = do
    let hasTyVars = or . map (Either.either Var.isTyVar tyHasFreeTyVars) $ args
    if hasTyVars
      then fail "funSpec"
      else do
        bodyMaybe <- liftQ $ getGlobalExpr f
        case bodyMaybe of
          Just body -> do
            (params',callerArgs',calleeArgs) <- fmap unzip3 . liftQ . mapM doArg $ args
            let params     = Maybe.catMaybes params'
            let callerArgs = Maybe.catMaybes callerArgs'
            let newBody    = mkLams params $ mkApps body calleeArgs
            newf           <- liftQ $ mkFunction f newBody
            let newExpr    = mkApps (Var newf) $ map Left callerArgs
            changed "funSpec" e newExpr
          Nothing -> fail "funSpec"
  where
    doArg :: Either Var Type -> NormalizeSession (Maybe Var, Maybe Var, Either Var Type)
    doArg (Left v) = do
      paramId <- mkBinderFor v "param"
      return (Just paramId, Just v, Left paramId)
    doArg (Right t) =
      return (Nothing, Nothing, Right t)

injectNonRepArguments :: NormalizeStep
injectNonRepArguments ctx expr@(App e arg)
  | (Var f, args) <- collectArgs e
  = do
    repr  <- liftQ $ isRepr arg
    bndrs <- fmap (Map.keys) $ (liftQ . lift . lift) $ Label.gets nsBindings
    let interesting = (arg `elem` bndrs)
    case interesting of
      True -> do
        bodyMaybe <- liftQ $ getGlobalExpr f
        case bodyMaybe of
          Just body -> do
            argParams <- liftQ $ mapM
                          (\v -> case v of
                              Left a  -> mkBinderFor   a "paramArg"
                              Right t -> mkTyBinderFor t "paramType"
                          ) args
            let newArgs = map (\v -> if Var.isTyVar v then Right (Type.mkTyVarTy v) else Left v) argParams
            let newBody = mkLams argParams $ mkApps body (newArgs ++ [Left arg])
            newf <- liftQ $ mkFunction f newBody
            let newExpr = mkApps (Var newf) args
            changed ("injectNonRepArguments: " ++ varStringUniq arg) expr newExpr
          Nothing -> fail "injectNonRepArguments"
      False -> fail "injectNonRepArguments"

injectNonRepArguments _ _ = fail "injectApplicableArguments"

--{- |
--This transformation takes a function (top level binding) that has a
--non-representable result (e.g., a tuple containing a function, or an
--Integer. The latter can occur in some cases as the result of the
--fromIntegerT function) and inlines enough of the function to make the
--result representable again.

--This is done by first normalizing the function and then \"inlining\"
--the result. Since no unrepresentable let bindings are allowed in
--normal form, we can be sure that all free variables of the result
--expression will be representable (Note that we probably can't
--guarantee that all representable parts of the expression will be free
--variables, so we might inline more than strictly needed).

--The new function result will be a tuple containing all free variables
--of the old result, so the old result can be rebuild at the caller.

--We take care not to inline dictionary id's, which are top level
--bindings with a non-representable result type as well, since those
--will never become VHDL signals directly. There is a separate
--transformation (inlinedict) that specifically inlines dictionaries
--only when it is useful.
---}
inlineNonRepResult :: NormalizeStep
inlineNonRepResult ctx expr | not (isApplicable expr) && not (hasFreeTyVars expr) = do
  case collectArgs expr of
    --(Var f, args) | Maybe.isNothing (Id.isClassOpId_maybe f) -> do
    (Var f, args) | not (Id.isDictId f) -> do
      repr <- liftQ $ isRepr expr
      case repr of
        False -> do
          bodyMaybe <- liftQ $ getGlobalExpr f
          case bodyMaybe of
            Just body -> do
              body' <- liftQ $ regenUniques body
              changed "inlineNonRepResult" expr (mkApps body' args)
          --bodyMaybe <- liftQ $ normalizeMaybe True f
          --case bodyMaybe of
          --  Just (_,body) -> trace ("Starting inlineNonRepResult: " ++ pprString f) $ do
          --    let (bndrs,binds,res) = splitNormalizedNonRep body
          --    case (hasFreeTyVars res) of
          --      -- Don't touch anything with free tyVars, since we
          --      -- can't return those.
          --      True -> fail "inlineNonRepResult"
          --      False -> do
                  --globalBndrs <- fmap (Map.keys) $ (liftQ . lift . lift) $ Label.gets nsBindings
                  --globalBindings <- (liftQ . lift . lift) $ Label.gets nsBindings
                  --let interesting var = Var.isLocalVar var && (var `notElem` globalBndrs)
                  --let freeVars        = VarSet.varSetElems $ termSomeFreeVars interesting res
                  --let freeVarTypes    = map Id.idType freeVars
                  --let nFreeVars       = length freeVars
                  --let fvsDataCon      = TysWiredIn.tupleCon BasicTypes.Boxed nFreeVars
                  --let fvsDataConId    = DataCon.dataConWorkId fvsDataCon
                  --let newRes          = case nFreeVars of 1 -> res ; _ -> mkApps (Var fvsDataConId) (map Right freeVarTypes ++ map Left freeVars)
                  --let newBody         = mkLams bndrs (LetRec binds newRes)
                  --error $ "DIE!"
                  --trace ("Finished inlineNonRepResult: " ++ pprString f) $ case nFreeVars of
                  --  0 -> do
                  --    changed "inlineNonRepResult" expr (mkApps res args)
                  --  _ -> do
                  --    repr' <- liftQ $ isRepr newBody
                  --    f' <- liftQ $ mkFunction f newBody
                  --    let newApp = mkApps (Var f') args
                  --    resBndr <- liftQ $ mkBinderFor newApp "fvs"
                  --    selCases <- liftQ $ case nFreeVars of
                  --                1 -> return [(Var resBndr)]
                  --                _ -> mapM (mkSelCase ("inlineNonRepResult: " ++ pprString (nFreeVars, newBody, args, newApp)) (Var resBndr) 0) [0 .. nFreeVars-1]
                  --    let binds = (resBndr,newApp):(zip freeVars selCases)
                  --    let letExpr = LetRec binds res
                  --    changed ("inlineNonRepResult(before,expr):\n" ++ pprString expr ++ "\ninlineNonRepResult(before,body):\n" ++ pprString body ++ "\ninlineNonRepResult(after, letExpr):\n" ++ pprString letExpr ++ "\ninlineNonRepResult(after, newBody):\n" ++ pprString (repr',newBody)) expr letExpr
            Nothing   -> fail "inlineNonRepResult"
        -- Don't touch representable expressions
        True -> fail "inlineNonRepResult"
    -- Not a reference or application of a top level function
    _ -> fail "inlineNonRepResult"

inlineNonRepResult _ _ = fail "inlineNonRepResult"

classopresolution c expr@(App (TyApp (Var sel) ty) dict) = do
  case (Id.isClassOpId_maybe sel) of
    Just cls -> do
      bodyMaybe <- liftQ $ getGlobalExpr dict
      case bodyMaybe of
        Just body -> do
          let selectorIds = Class.classAllSelIds cls
          let selIdN = List.elemIndex sel selectorIds
          case selIdN of
            Just n -> do
              selCase <- liftQ $ mkSelCase "classopresolution" body 0 n
              changed "classopresolution" expr selCase
            Nothing -> fail "classopresolution"
        Nothing -> fail "classopresolution"
    Nothing -> fail "classopresolution"

classopresolution _ _ = fail "classopresolution"
