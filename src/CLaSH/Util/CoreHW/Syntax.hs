module CLaSH.Util.CoreHW.Syntax
  ( module CLaSH.Util.CoreHW.Syntax
  , DataCon, Var, Literal, Type
  )
where

-- GHC API
import DataCon (DataCon)
import Literal (Literal)
import Type    (Type)
import Var     (Var, TyVar)

data Term
  = Var    Var
  | Value  Value
  | TyApp  Term         Type
  | App    Term         Var
  | OpApp  PrimOp       [Term]
  | Case   Term         Type [(AltCon,Term)]
  | LetRec [(Var,Term)] Term

data Value
  = Literal  Literal
  | TyLambda TyVar   Term
  | Lambda   Var     Term
  | Data     DataCon [Type] [Var]

data PrimOp
  = PrimCall Var

data AltCon
  = DataAlt    DataCon [TyVar] [Var]
  | LiteralAlt Literal
  | DefaultAlt
