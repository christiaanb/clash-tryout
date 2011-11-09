module CLaSH.Util.CoreHW.Syntax
  ( module CLaSH.Util.CoreHW.Syntax
  , DataCon, Var, TyVar, Literal, Type
  )
where

-- GHC API
import DataCon (DataCon)
import Literal (Literal)
import Type    (Type)
import Var     (Var, TyVar)

data Term
  = Var      Var
  | Literal  Literal
  | Data     DataCon
  | Prim     Var
  | TyLambda TyVar        Term
  | Lambda   Var          Term
  | TyApp    Term         Type
  | App      Term         Term
  | Case     Term         Type   [(AltCon,Term)]
  | LetRec   [(Var,Term)] Term

data AltCon
  = DataAlt    DataCon [Var]
  | LiteralAlt Literal
  | DefaultAlt
