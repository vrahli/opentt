default:
	agda --ghc-flag="-j4" +RTS -M5G -RTS --compile all.lagda
