module CLaSH.Netlist.Types
where

-- External Modules
import Control.Monad.Error (ErrorT)
import Control.Monad.State (State)
import qualified Data.Label
import Data.Map (Map,empty)

-- GHC API
import qualified CoreSyn
import qualified Type

newtype OrdType = OrdType Type.Type
instance Eq OrdType where
  (OrdType a) == (OrdType b) = Type.eqType a b
instance Ord OrdType where
  compare (OrdType a) (OrdType b) = Type.cmpType a b

data HWType = BitType
            | SignedType Int
            | SumType     String [String]
            | ProductType String [HWType]
            | SPType      String [(String,[HWType])]
            | UnitType
            | ClockType
            | Invalid String
  deriving (Eq,Ord,Show)

type Ident = String

data Module = Module {
    _modName    :: Ident
  , _modInputs  :: [(Ident,HWType)]
  , _modOutptus :: [(Ident,HWType)]
  , _modDecl    :: [Decl]
  } deriving (Eq,Ord,Show)
  
data Decl = NetDecl     Ident HWType (Maybe Expr)
          | InstDecl    Ident Ident [(Ident,Expr)] [(Ident,Expr)] [(Ident,Expr)]
          | ProcessDecl [(Event,Stmt)]
  deriving (Eq,Ord,Show)
          
data Event = Event Expr Edge
  deriving (Eq,Ord,Show)

data Edge = PosEdge
          | NegEdge
          | AsyncHigh
          | AsyncLow
  deriving (Eq,Ord,Show)
          
data Expr = ExprLit     ExprLit
          | ExprVar     Ident
          | ExprSlice   Ident Expr Expr
          | ExprConcat  [Expr]
          | ExprCond    Expr Expr Expr
          | ExprUnary   UnaryOp Expr
          | ExprBinary  BinaryOp Expr Expr
          | ExprFunCall Ident [Expr]
  deriving (Eq,Ord,Show)
          
data ExprLit = ExprNum       Integer
             | ExprBit       Bit
             | ExprBitVector [Bit]
  deriving (Eq,Ord,Show)

data Bit = H | L | U | Z
  deriving (Eq,Ord,Show)

data Stmt = Assign LValue Expr
          | IfSt Expr Stmt (Maybe Stmt)
          | CaseSt Expr [([Expr],Stmt)] (Maybe Stmt)
          | Seq [Stmt]
          | FunCallStmt Ident [Expr]
  deriving (Eq,Ord,Show)
          
type LValue = Expr

data UnaryOp = Neg
  deriving (Eq,Ord,Show)

data BinaryOp = Plus | Minus | Times | Equals | NotEquals | And | Or | Xor
  deriving (Eq,Ord,Show)

data NetlistState = NetlistState 
  { _nlTypes      :: Map OrdType HWType
  , _nlModCnt     :: Integer
  , _nlMods       :: Map CoreSyn.CoreBndr Module
  , _nlNormalized :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  }

empytNetlistState = NetlistState empty 0 empty empty

Data.Label.mkLabels [''NetlistState]

type NetlistSession = ErrorT String (State NetlistState)
