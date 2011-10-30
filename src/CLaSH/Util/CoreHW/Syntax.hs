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
  | TyLambda TyVar        Term
  | Lambda   Var          Term
  | Data     DataCon      [Type] [Var]
  | TyApp    Term         Type
  | App      Term         Var
  | Case     Term         Type   [(AltCon,Term)]
  | LetRec   [(Var,Term)] Term

data AltCon
  = DataAlt    DataCon [TyVar] [Var]
  | LiteralAlt Literal
  | DefaultAlt
