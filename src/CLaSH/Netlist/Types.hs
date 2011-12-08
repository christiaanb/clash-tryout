module CLaSH.Netlist.Types
where

-- External Modules
import Control.Monad.Error (ErrorT)
import Control.Monad.State.Strict (State)
import qualified Data.Label
import Data.Map (Map,empty)

-- GHC API
import qualified TyCon
import qualified Type

-- Internal Modules
import CLaSH.Util.CoreHW.Syntax (Term,Var)
import CLaSH.Util.CoreHW.Types  (OrdType)

type Size = Int

data HWType = BitType
            | BoolType
            | IntegerType
            | ByteArrayType
            | SignedType Size
            | UnsignedType Size
            | VecType Size HWType
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
  , _modOutputs :: [(Ident,HWType)]
  , _modDecls   :: [Decl]
  } deriving (Eq,Ord,Show)

data Decl = NetDecl     Ident HWType (Maybe Expr)
          | NetAssign   Ident Expr
          | InstDecl    Ident Ident [(Ident,Expr)] [(Ident,Expr)] [(Ident,Expr)]
          | ProcessDecl [(Event,Stmt)]
          | CommentDecl String
  deriving (Eq,Ord,Show)

type ConstExpr = Expr

data Event = Event Expr Edge
  deriving (Eq,Ord,Show)

data Edge = PosEdge
          | NegEdge
          | AsyncHigh
          | AsyncLow
  deriving (Eq,Ord,Show)

data Expr = ExprLit     (Maybe Size) ExprLit
          | ExprVar     Ident
          | ExprIndex   Ident Expr
          | ExprSlice   Ident Expr Expr
          | ExprAll     Expr
          | ExprConcat  [Expr]
          | ExprCase    Expr [([ConstExpr], Expr)] (Maybe Expr)
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

data UnaryOp = LNeg
  deriving (Eq,Ord,Show)

data BinaryOp = Plus | Minus | Times | Equals | NotEquals | And | Or | Xor
  deriving (Eq,Ord,Show)

data NetlistState = NetlistState
  { _nlTypes      :: Map OrdType HWType
  , _nlModCnt     :: Integer
  , _nlVarCnt     :: Integer
  , _nlTypeCnt    :: Integer
  , _nlMods       :: Map Var Module
  , _nlNormalized :: Map Var Term
  , _nlTfpSyn     :: Map OrdType Integer
  }

empytNetlistState = NetlistState empty 0 0 0 empty empty empty

Data.Label.mkLabels [''NetlistState]

type NetlistSession = ErrorT String (State NetlistState)
