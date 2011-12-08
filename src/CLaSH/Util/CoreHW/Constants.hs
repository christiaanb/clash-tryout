module CLaSH.Util.CoreHW.Constants
  ( builtinIds
  , builtinDicts
  , builtinDFuns
  , builtinDataCons
  , builtinFuns
  )
where

builtinIds :: [String]
builtinIds = concat [builtinDicts,builtinDFuns,builtinDataCons,builtinFuns]

builtinDicts :: [String]
builtinDicts = ["$dPositiveT","$dNaturalT","$dIntegerT"]

builtinDFuns :: [String]
builtinDFuns = ["$fShowUnsigned","$fEqInteger","$fPositiveTx","$fNaturalTx",
  "$fArrowComponent","$fArrowLoopComponent"]

builtinDataCons :: [String]
builtinDataCons = ["I#","Int#"]

builtinFuns :: [String]
builtinFuns = ["xorB","andB","notB","orB","delay",
  "+>>","vlast", "singleton", "empty", "+>","smallInteger","eqUnsigned",
  "neqUnsigned","plusUnsigned", "minUnsigned", "timesUnsigned",
  "negateUnsigned", "unsignedFromInteger", "absUnsigned", "signumUnsigned",
  "vcopyn", "vcopy", "vfoldl", "vzipWith"]
