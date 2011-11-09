module CLaSH.Netlist.GenVHDL
  ( genVHDL
  )
where

-- External Modules
import Text.PrettyPrint
import Data.Maybe (catMaybes)
import Data.List (nub)

-- Internal Modules
import CLaSH.Netlist.Tools
import CLaSH.Netlist.Types

genVHDL :: Module -> [String] -> (String,String)
genVHDL m others = (_modName m, render vhdl ++ "\n")
  where
    vhdl = imports others $$
           entity m $$
           architecture m

imports :: [String] -> Doc
imports others = vcat
  [ text "library IEEE" <> semi
  , text "use IEEE.STD_LOGIC_1164.ALL" <> semi
  , text "use IEEE.NUMERIC_STD.ALL" <> semi
  ] $$ vcat [
      text ("use " ++ other) <> semi
    | other <- others
    ]

entity :: Module -> Doc
entity m = text "entity" <+> text (_modName m) <+> text "is" $$
            nest 2 (text "port" <> parens (vcat $ punctuate semi ports) <> semi) $$
            text "end" <+> text "entity" <+> text (_modName m) <> semi

  where ports = [text i <+> colon <+> text "in" <+> slv_type ran | (i,ran) <- _modInputs m ] ++
                [text i <+> colon <+> text "out" <+> slv_type ran | (i,ran) <- _modOutptus m ]

architecture :: Module -> Doc
architecture m = text "architecture" <+> text "str" <+> text "of" <+>  text (_modName m) <+> text "is" $$
                 nest 2 (decls (_modDecls m)) $$
                 text "begin" $$
                 nest 2 (insts (_modDecls m)) $$
                 text "end" <+> text "architecture" <+> text "str" <> semi

decls :: [Decl] -> Doc
decls [] = empty
decls ds = let
    dsDoc = (vcat $ punctuate semi $ catMaybes $ map decl ds)
  in
    if (isEmpty dsDoc)
      then empty
      else dsDoc <> semi

decl :: Decl -> Maybe Doc
decl (NetDecl i r Nothing) = Just $
  text "signal" <+> text i <+> colon <+> slv_type r

decl (NetDecl i r (Just init)) = Just $
  text "signal" <+> text i <+> colon <+> slv_type r <+> text ":=" <+> expr init

decl _d = Nothing

insts ::  [Decl] -> Doc
insts [] = empty
insts is = case catMaybes $ zipWith inst gensyms is of
             [] -> empty
             is' -> (vcat $ punctuate semi is') <> semi
  where gensyms = ["proc" ++ show i | i <- [(0::Integer)..]]

inst :: String -> Decl -> Maybe Doc
inst _ (NetAssign i e) = Just $ text i <+> text "<=" <+> expr e

inst gensym proc@(ProcessDecl evs) = Just $
    text gensym <+> colon <+> text "process" <> senlist <+> text "is" $$
    text "begin" $$
    nest 2 (pstmts evs) $$
    text "end process" <+> text gensym
  where senlist = parens $ cat $ punctuate comma $ map expr $   mkSensitivityList proc

inst _ (InstDecl nm inst gens ins outs) = Just $
  text inst <+> colon <+> text "entity" <+> text nm $$
       gs $$
       ps
 where
   gs | null gens = empty
      | otherwise =
        text "generic map" <+>
         (parens (cat (punctuate comma  [text i <+> text "=>" <+> expr e | (i,e) <- gens])))
   -- Assume that ports is never null
   ps = text "port map" <+>
         parens (cat (punctuate comma  [text i <+> text "=>" <+> expr e | (i,e) <- (ins ++ outs)]))

inst _ (CommentDecl msg) = Just $
	(vcat [ text "--" <+> text m | m <- lines msg ])

inst _ _d = Nothing

pstmts :: [(Event, Stmt)] -> Doc
pstmts ss = (vcat $ zipWith mkIf is ss)  $$ text "end if" <> semi
  where is = (text "if"):(repeat (text "elsif"))
        mkIf i (p,s) = i <+> nest 2 (event p) <+> text "then" $$
                       nest 2 (stmt s)

event :: Event -> Doc
event (Event i PosEdge)   = text "rising_edge" <> parens (expr i)
event (Event i NegEdge)   = text "falling_edge" <> parens (expr i)
event (Event i AsyncHigh) = expr i <+> text "= '1'"
event (Event i AsyncLow)  = expr i <+> text "= '0'"

stmt :: Stmt -> Doc
stmt (Assign l r) = expr l <+> text "<=" <+> expr r <> semi

to_bits :: Integral a => Int -> a -> [Bit]
to_bits size val = map (\x -> if odd x then H else L)
                   $ reverse
                   $ take size
                   $ map (`mod` 2)
                   $ iterate (`div` 2)
                   $ val

bit_char :: Bit -> Char
bit_char H = '1'
bit_char L = '0'
bit_char U = 'U'
bit_char Z = 'Z'

bits :: [Bit] -> Doc
bits = doubleQuotes . text . map bit_char

expr_lit :: Maybe Size -> ExprLit -> Doc
expr_lit Nothing (ExprNum i)          = int $ fromIntegral i
expr_lit (Just sz) (ExprNum i)        = bits (to_bits sz i)
expr_lit _ (ExprBit x)                = quotes (char (bit_char x))

expr :: Expr -> Doc
expr (ExprLit mb_sz lit) = expr_lit mb_sz lit
expr (ExprVar n) = text n
expr (ExprIndex s i) = text s <> parens (expr i)
expr (ExprSlice s h l) = text s <> parens (expr h <+> text "downto" <+> expr l)
expr (ExprConcat ss) = hcat $ punctuate (text " & ") (map expr ss)
expr (ExprUnary op e) = lookupUnary op (expr e)
expr (ExprBinary op a b) = lookupBinary op (expr a) (expr b)
expr (ExprFunCall f args) = text f <> parens (cat $ punctuate comma $ map expr args)
expr (ExprCond c t e) = expr t <+> text "when" <+> expr c <+> text "else" $$ expr e
expr (ExprCase _ [] Nothing) = error "VHDL does not support non-defaulted ExprCase"
expr (ExprCase _ [] (Just e)) = expr e
expr (ExprCase e (([],_):alts) def) = expr (ExprCase e alts def)
expr (ExprCase e ((p:ps,alt):alts) def) =
	expr (ExprCond (ExprBinary Equals e p) alt (ExprCase e ((ps,alt):alts) def))

lookupUnary :: UnaryOp -> Doc -> Doc
lookupUnary op e = text (unOp op) <> parens e

unOp :: UnaryOp -> String
unOp LNeg = "not"

lookupBinary :: BinaryOp -> Doc -> Doc -> Doc
lookupBinary op a b = parens $ a <+> text (binOp op) <+> b

binOp :: BinaryOp -> String
binOp And = "and"
binOp Xor = "xor"
binOp Or  = "or"
binOp Equals = "="
binOp Plus = "+"
binOp Minus = "-"

mkSensitivityList :: Decl -> [Expr]
mkSensitivityList (ProcessDecl evs) = nub event_names
  where event_names =
		map (\ (e,_) -> case e of
				 Event (ExprVar name) _ -> ExprVar name
				 _ -> error $ "strange form for mkSensitivityList " ++ show e
		    ) evs

slv_type :: HWType -> Doc
slv_type BitType = text "std_logic"
slv_type BoolType = text "std_logic"
slv_type ClockType = text "std_logic"
slv_type IntegerType = text "integer"
slv_type (UnsignedType len) = text "std_logic_vector" <> range (ExprLit Nothing $ ExprNum $ toInteger $ len - 1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype@(ProductType _ _) =  text "std_logic_vector" <> range (ExprLit Nothing $ ExprNum $ toInteger $ htypeSize hwtype - 1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype@(SumType _ _) = text "std_logic_vector" <> range (ExprLit Nothing $ ExprNum $ toInteger $ htypeSize hwtype - 1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype@(SPType "Integer" _) = text "integer"
slv_type hwtype@(SPType _ _) = text "std_logic_vector" <> range (ExprLit Nothing $ ExprNum $ toInteger $ htypeSize hwtype -1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype = error $ "slv_type: " ++ show hwtype
--slv_type hwtype@(VecType s e) = text "array" <+> range (ExprLit Nothing $ ExprNum $ toInteger $ s - 1, ExprLit Nothing $ ExprNum 0) <+> text "of" <+> slv_type e

range :: (Expr,Expr) -> Doc
range (high, low) = parens (expr high <+> text "downto" <+> expr low)
