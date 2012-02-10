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
  "$fArrowComponent","$fArrowLoopComponent","$fShowSigned","$fNumInt"]

builtinDataCons :: [String]
builtinDataCons = ["I#","Int#","Signed","Unsigned"]

builtinFuns :: [String]
builtinFuns = concat
  [ stateFuns
  , bitFuns
  , vecFuns
  --, unsignedFuns
  --, signedFuns
  , numFuns
  , eqFuns
  , ordFuns
  , literalFuns
  ]
  where
    stateFuns = ["delayBuiltin","blockRamBuiltin"]

    bitFuns = ["xorB","andB","notB","orB",".&.","xor","$c.&.","$cxor","$c.|."
              ,"$ccomplement", "$cshift", "$crotate", "$cbit", "$csetBit"
              ,"$cclearBit", "$ccomplementBit", "$ctestBit", "$cbitSize"
              ,"$cisSigned","$cshiftL", "$cshiftR", "$crotateL", "$crotateR"
              ]

    vecFuns =
      [ "+>>","<<+","vinit","vlast","singleton","empty","+>","vcopyn"
      , "vcopy","vfoldl","vzipWith","vmap","!","vreplace"
      ]

    numFuns = ["+","*","-","negate","abs","signum","fromInteger"]

    eqFuns = ["==","/="]

    ordFuns = ["compare","<",">=",">","<=","max","min"]

    unsignedFuns =
      ["eqUnsigned","neqUnsigned","plusUnsigned","minUnsigned","timesUnsigned"
      ,"negateUnsigned","unsignedFromInteger","absUnsigned","signumUnsigned"
      ]

    signedFuns =
      ["eqSigned", "neqSigned","plusSigned", "minSigned", "timesSigned"
      ,"negateSigned", "signedFromInteger", "absSigned", "signumSigned"
      ]

    literalFuns = ["timesInteger","plusInteger","smallInteger"]
