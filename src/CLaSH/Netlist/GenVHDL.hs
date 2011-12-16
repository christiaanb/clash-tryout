module CLaSH.Netlist.GenVHDL
  ( genVHDL
  , genTypes
  )
where

-- External Modules
import Text.PrettyPrint
import Data.Either (either)
import Data.Maybe (catMaybes)
import Data.List (nub)

-- Internal Modules
import CLaSH.Netlist.Tools
import CLaSH.Netlist.Types
import CLaSH.Util.Pretty (zEncodeString)

genTypes :: [HWType] -> String
genTypes elTypes = render vhdl ++ "\n"
  where
    vhdl = tyImports $$
           package elTypes

package :: [HWType] -> Doc
package elTypes = text "package types is" $$
                  nest 2 ((case elTypes of [] -> text ""; _ -> (vcat $ punctuate semi vecTys) <> semi) $$
                          (vcat vecFuns)) $$
                  text "end package types" <> semi $$
                  text "package body types is" $$
                  nest 2 (vcat vecBoolConvBody) $$
                  nest 2 (vcat $ map toVecFunBody elTypes) $$
                  nest 2 (vcat $ map fromVecFunBody elTypes) $$
                  text "end package body types" <> semi
  where
    vecTys  = [text "type" <+> text (vecTyName t) <+> text "is array (natural range <>) of" <+> (slv_type t) | t <- elTypes]
    vecFuns = [text "function" <+> text "toSLV" <+> parens (text "bin" <+> colon <+> text "boolean") <+> text "return std_logic_vector" <> semi
              ,text "function" <+> text "fromSLV" <+> parens (text "vin" <+> colon <+> text "std_logic_vector") <+> text "return boolean" <> semi
              ] ++
              [text "function" <+> text "toSLV" <+> parens (text "ain" <+> colon <+> text (vecTyName t)) <+> text "return std_logic_vector" <> semi $$
               text "function" <+> text "fromSLV" <+> parens (text "vin" <+> colon <+> text "std_logic_vector") <+> text "return" <+> text (vecTyName t) <> semi
              | t <- elTypes
              ]

vecBoolConvBody :: [Doc]
vecBoolConvBody =
  [ text "function" <+> text "toSLV" <+> parens (text "bin" <+> colon <+> text "boolean") <+> text "return std_logic_vector is" $$
    nest 4 (text "variable res" <+> colon <+> text "std_logic_vector" <+> parens (text "0 downto 0" ) <> semi) $$
    nest 2 (text "begin" $$
            nest 2 (text "if bin then" $$
                    nest 2 (text "res := \"1\"" <> semi) $$
                    text "else" $$
                    nest 2 (text "res := \"0\"" <> semi) $$
                    text "end if" <> semi $$
                    text "return res" <> semi
                   ) $$
            text "end" <> semi
           )
  , text "function" <+> text "fromSLV" <+> parens (text "vin" <+> colon <+> text "std_logic_vector") <+> text "return boolean is" $$
    nest 4 (text "variable res" <+> colon <+> text "boolean" <> semi $$
            text "variable tmp" <+> colon <+> text "std_logic" <> semi) $$
    nest 2 (text "begin" $$
            nest 2 (text "tmp := vin(0)" <> semi $$
                    text "if tmp = \'1\' then" $$
                    nest 2 (text "res := true" <> semi) $$
                    text "else" $$
                    nest 2 (text "res := false" <> semi) $$
                    text "end if" <> semi $$
                    text "return res" <> semi
                   ) $$
            text "end" <> semi
           )
  ]

toVecFunBody :: HWType -> Doc
toVecFunBody elTy =
  text "function" <+> text "toSLV" <+> parens (text "ain" <+> colon <+> text (vecTyName elTy)) <+> text "return std_logic_vector is" $$
  nest 4 (text "variable res" <+> colon <+> text "std_logic_vector" <+> parens (text "ain'length *" <+> text elTySize <+> text "- 1 downto 0" ) <> semi) $$
  nest 2 (text "begin" $$
          nest 2 (text "for n in 0 to (ain'length - 1) loop" $$
                  nest 2 (text "res" <> parens (text "(n+1) *" <+> text elTySize <+> text "- 1 downto" <+> parens (text "n*" <> text elTySize)) <+>
                          text ":=" <+> text (render $ expr (toSLV elTy (ExprIndex "ain" (ExprVar "n")))) <> semi) $$
                  text "end loop" <> semi $$
                  text "return res" <> semi
                 ) $$
          text "end" <> semi
         )
  where
    elTySize = show . htypeSize $ elTy

fromVecFunBody :: HWType -> Doc
fromVecFunBody elTy =
  text "function" <+> text "fromSLV" <+> parens (text "vin" <+> colon <+> text "std_logic_vector") <+> text "return" <+> text (vecTyName elTy) <+> text "is" $$
  nest 4 (text "variable res" <+> colon <+> text (vecTyName elTy) <+> parens (text "vin'length /" <+> text elTySize <+> text "- 1 downto 0" ) <> semi) $$
  nest 2 (text "begin" $$
          nest 2 (text "for n in 0 to (res'length - 1) loop" $$
                  nest 2 (text "res(n) :=" <+>
                          text (render $ expr (fromSLV elTy (ExprSlice "vin" (ExprVar $ "(n+1) * " ++ elTySize ++ " - 1") (ExprVar $ "n*" ++ elTySize)))) <> semi) $$
                  text "end loop" <> semi $$
                  text "return res" <> semi
                 ) $$
          text "end" <> semi
         )
  where
    elTySize = show . htypeSize $ elTy

tyImports :: Doc
tyImports = vcat
  [ text "library IEEE" <> semi
  , text "use IEEE.STD_LOGIC_1164.ALl" <> semi
  , text "use IEEE.NUMERIC_STD.ALL" <> semi
  ]

genVHDL :: [String] -> Module -> (String,String)
genVHDL others m = (_modName m, render vhdl ++ "\n")
  where
    vhdl = imports others $$
           entity m $$
           architecture m

imports :: [String] -> Doc
imports others = vcat
  [ text "library IEEE" <> semi
  , text "use IEEE.STD_LOGIC_1164.ALL" <> semi
  , text "use IEEE.NUMERIC_STD.ALL" <> semi
  , text "use STD.TEXTIO.ALL" <> semi
  ] $$ vcat [
      text ("use " ++ other) <> semi
    | other <- others
    ]

entity :: Module -> Doc
entity m = text "entity" <+> text (_modName m) <+> text "is" $$
            (case ports of [] -> text "" ; p -> nest 2 (text "port" <> parens (vcat $ punctuate semi p) <> semi)) $$
            text "end" <+> text "entity" <+> text (_modName m) <> semi

  where ports = [text i <+> colon <+> text "in" <+> slv_type ran | (i,ran) <- _modInputs m ] ++
                [text i <+> colon <+> text "out" <+> slv_type ran | (i,ran) <- _modOutputs m ]

architecture :: Module -> Doc
architecture m = text "architecture" <+> text "str" <+> text "of" <+>  text (_modName m) <+> text "is" $$
                 nest 2 (decls (nub $ _modDecls m)) $$
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
  text "signal" <+> text (mkVHDLBasicId i) <+> colon <+> slv_type r

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
    nest 2 (case evs of Left evs' -> pstmts evs'; Right stmts -> vcat (map stmt stmts)) $$
    text "end process" <+> text gensym
  where senlist = either (\_ -> parens $ cat $ punctuate comma $ map expr $ mkSensitivityList proc) (\_ -> text "") evs

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

inst _ (ClockDecl ident int e) = Just $
  text ident <+> text "<= not" <+> text ident <+> text "after" <+> text (show $ (fromIntegral int) / 2.0) <+> text "ns when" <+> expr e

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
stmt (Seq ss) = vcat (map stmt ss)
stmt (Wait Nothing) = text "wait" <> semi
stmt (Wait (Just t)) = text "wait for" <+> text (show t) <+> text "ns" <> semi
stmt (Assert e i1 i2) = text "assert" <+> (expr e) <+> text "report" <+> parens (text "\"expected: \" &" <+> (expr i2) <+> text "& \", actual: \" &" <+> (expr i1)) <+> text "severity error" <> semi

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
expr_lit _ (ExprBool b)               = text (show b)
expr_lit Nothing (ExprBitVector xs)   = bits xs

expr :: Expr -> Doc
expr (ExprLit mb_sz lit) = expr_lit mb_sz lit
expr (ExprVar n) = text n
expr (ExprIndex s i) = text s <> parens (expr i)
expr (ExprSlice s h l) = text s <> parens (expr h <+> text "downto" <+> expr l)
expr (ExprAll e) = parens (text "others =>" <+> expr e)
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
expr (ExprDelay [])         = error "delay expression should have atleast one value"
expr (ExprDelay [(e,n)])    = (expr e) <+> text "after" <+> text (show n) <+> text "ns"
expr (ExprDelay ((e,n):es)) = (expr e) <+> text "after" <+> text (show n) <+> text "ns" <> comma $$ (expr (ExprDelay es))

lookupUnary :: UnaryOp -> Doc -> Doc
lookupUnary op e = text (unOp op) <> parens e

unOp :: UnaryOp -> String
unOp LNeg = "not"
unOp Neg  = "-"

lookupBinary :: BinaryOp -> Doc -> Doc -> Doc
lookupBinary op a b = parens $ a <+> text (binOp op) <+> b

binOp :: BinaryOp -> String
binOp And = "and"
binOp Xor = "xor"
binOp Or  = "or"
binOp Equals = "="
binOp Plus = "+"
binOp Minus = "-"
binOp Times = "*"

mkSensitivityList :: Decl -> [Expr]
mkSensitivityList (ProcessDecl (Left evs)) = nub $ concat event_names
  where event_names =
		map (\e -> case e of
                (Event (ExprVar name) AsyncLow, Assign _ (ExprVar name')) -> [ExprVar name, ExprVar name'];
      				  (Event (ExprVar name) _, _)                    -> [ExprVar name];
      				  _                                              -> error $ "strange form for mkSensitivityList " ++ show e
		    ) evs

tyName :: HWType -> String
tyName BitType             = "std_logic"
tyName BoolType            = "boolean"
tyName (ClockType _)       = "std_logic"
tyName (ResetType _)       = "std_logic"
tyName (UnsignedType len)  = "unsigned" ++ show len
tyName (SignedType len)    = "signed" ++ show len
tyName (VecType _ e)       = vecTyName e
tyName t@(ProductType n _) = zEncodeString n
tyName (SumType n _)       = zEncodeString n
tyName t@(SPType n _)      = zEncodeString n

vecTyName e = (tyName e) ++ "_vector"

slv_type :: HWType -> Doc
slv_type BitType                  = text "std_logic"
slv_type BoolType                 = text "boolean"
slv_type (ClockType _)            = text "std_logic"
slv_type (ResetType _)            = text "std_logic"
slv_type (UnsignedType len)       = text "unsigned" <> range (ExprLit Nothing $ ExprNum $ toInteger $ len - 1, ExprLit Nothing $ ExprNum 0)
slv_type (SignedType len)         = text "signed" <> range (ExprLit Nothing $ ExprNum $ toInteger $ len - 1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype@(VecType s e)     = text (tyName hwtype) <> range (ExprLit Nothing $ ExprNum $ toInteger $ s - 1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype@(ProductType _ _) = text "std_logic_vector" <> range (ExprLit Nothing $ ExprNum $ toInteger $ htypeSize hwtype - 1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype@(SumType _ _)     = text "std_logic_vector" <> range (ExprLit Nothing $ ExprNum $ toInteger $ htypeSize hwtype - 1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype@(SPType _ _)      = text "std_logic_vector" <> range (ExprLit Nothing $ ExprNum $ toInteger $ htypeSize hwtype - 1, ExprLit Nothing $ ExprNum 0)
slv_type hwtype                   = error $ "slv_type: " ++ show hwtype

range :: (Expr,Expr) -> Doc
range (high, low) = parens (expr high <+> text "downto" <+> expr low)
