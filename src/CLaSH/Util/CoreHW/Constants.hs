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
  "$fArrowComponent","$fArrowLoopComponent","$fShowSigned"]

builtinDataCons :: [String]
builtinDataCons = ["I#","Int#","Signed","Unsigned"]

builtinFuns :: [String]
builtinFuns = ["timesInteger","plusInteger","xorB","andB","notB","orB","delay",
  "+>>","vlast", "singleton", "empty", "+>","smallInteger","eqUnsigned",
  "neqUnsigned","plusUnsigned", "minUnsigned", "timesUnsigned",
  "negateUnsigned", "unsignedFromInteger", "absUnsigned", "signumUnsigned",
  "eqSigned", "neqSigned","plusSigned", "minSigned", "timesSigned",
  "negateSigned", "signedFromInteger", "absSigned", "signumSigned",
  "vcopyn", "vcopy", "vfoldl", "vzipWith"]
