{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
module CLaSH.Util.Core.Show where

-- GHC API
import qualified CoreSyn
import Outputable (Outputable, showSDoc, ppr)
import qualified TyCon

deriving instance (Show b) => Show (CoreSyn.Expr b)
deriving instance (Show b) => Show (CoreSyn.Bind b)
deriving instance Show CoreSyn.Note
deriving instance Show TyCon.SynTyConRhs

instance Show TyCon.TyCon where
  show t | TyCon.isAlgTyCon t && not (TyCon.isTupleTyCon t) =
           showtc "AlgTyCon" ""
         | TyCon.isSynTyCon t =
           showtc "SynTyCon" (", synTcRhs = " ++ synrhs)
         | TyCon.isTupleTyCon t =
           showtc "TupleTyCon" ""
         | TyCon.isFunTyCon t =
           showtc "FunTyCon" ""
         | TyCon.isPrimTyCon t =
           showtc "PrimTyCon" ""
         | TyCon.isSuperKindTyCon t =
           showtc "SuperKindTyCon" ""
         | otherwise = 
           "_OTHER tycon?:(" ++ showSDoc (ppr t) ++ ")_"
      where
        showtc con extra = "(" ++ con ++ " {tyConName = " ++ name ++ extra ++ ", ...})"
        name = show (TyCon.tyConName t)
        synrhs = show (TyCon.synTyConRhs t)

instance (Outputable x) => Show x where
  show x = "___" ++ showSDoc (ppr x) ++ "___"
