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

genVHDL :: Module -> [String] -> String
genVHDL m others = render vhdl ++ "\n"
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
decls ds = (vcat $ punctuate semi $ catMaybes $ map decl ds) <> semi

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

bit_char :: Bit -> Char
bit_char H = '1'
bit_char L = '0'
bit_char U = 'U'  -- 'U' means uninitialized,
                  -- 'X' means forced to unknown.
                  -- not completely sure that 'U' is the right choice here.
bit_char Z = 'Z'

expr_lit :: ExprLit -> Doc
expr_lit (ExprNum i)          = int $ fromIntegral i
expr_lit (ExprBit x)                = quotes (char (bit_char x))

expr :: Expr -> Doc
expr (ExprLit lit) = expr_lit lit
expr (ExprVar n) = text n
expr (ExprSlice s h l)
  | h >= l = text s <> parens (expr h <+> text "downto" <+> expr l)
  | otherwise = text s <> parens (expr h <+> text "to" <+> expr l)

expr (ExprConcat ss) = hcat $ punctuate (text " & ") (map expr ss)

mkSensitivityList :: Decl -> [Expr]
mkSensitivityList (ProcessDecl evs) = nub event_names
  where event_names =
	 	--   AJG: This is now *only* based on the 'Event' vars, nothing else.
		map (\ (e,_) -> case e of
				 Event (ExprVar name) _ -> ExprVar name
				 _ -> error $ "strange form for mkSensitivityList " ++ show e
		    ) evs

slv_type :: HWType -> Doc
slv_type BitType = text "std_logic"
slv_type ClockType = text "std_logic"
slv_type hwtype@(ProductType _ _) =  text "std_logic_vector" <> range (ExprLit $ ExprNum $ toInteger $ htypeSize hwtype - 1, ExprLit $ ExprNum $ 0)

range :: (Expr,Expr) -> Doc
range (high, low) = parens (expr high <+> text "downto" <+> expr low)
