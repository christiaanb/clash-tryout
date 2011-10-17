module CLaSH.Util.CoreHW.Tools
  ( nameString
  , termType
  , varString
  )
where

-- GHC API
import DataCon (dataConWorkId)
import Id      (idType)
import Literal (literalType)
import Name    (Name, nameOccName)
import OccName (occNameString)
import Type    (Type, applyTy, applyTys, mkForAllTy, mkFunTy, splitFunTy)
import Var     (Var,varName)

-- Internal Modules
import CLaSH.Util
import CLaSH.Util.CoreHW.Syntax

nameString ::
  Name
  -> String
nameString = occNameString . nameOccName

varString ::
  Var
  -> String
varString = nameString . varName

termType ::
  Term
  -> Type
termType e = case e of
  Var x          -> idType x
  Value v        -> valueType v
  TyApp e a      -> termType e `applyTy` a
  App e x        -> termType e `applyFunTy` idType x
  OpApp p es     -> (opTy p) `applyTys` (map termType es)
  Case _ ty alts -> ty
  LetRec _ e     -> termType e

valueType ::
  Value
  -> Type
valueType v = case v of
  Literal l     -> literalType l
  TyLambda tv e -> tv `mkForAllTy` termType e
  Lambda v e    -> idType v `mkFunTy` termType e
  Data dc as xs -> (idType (dataConWorkId dc) `applyTys` as) `applyFunTys` map idType xs

opTy ::
  PrimOp
  -> Type
opTy (PrimCall x) = idType x

applyFunTy ::
  Type
  -> Type
  -> Type
applyFunTy funTy argTy = resTy
  where
    (resTy, _) = splitFunTy funTy

applyFunTys ::
  Type
  -> [Type]
  -> Type
applyFunTys = foldl' applyFunTy
