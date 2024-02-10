default:
	agda --ghc-flag="-j4" +RTS -M6G -RTS --compile all.lagda

%.lagda:
	agda --ghc-flag="-j4" +RTS -M6G -RTS --compile $@
