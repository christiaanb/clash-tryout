module CLaSH.Driver.Tools
  ( isTopEntity
  )
where

-- GHC API
import qualified Name
import qualified Var

isTopEntity
  :: Var.Var
  -> Bool
isTopEntity bind =
  "topEntity" == (Name.occNameString . Name.nameOccName . Name.getName) bind
