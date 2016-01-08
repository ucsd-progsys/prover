{-# LANGUAGE OverloadedStrings #-}

module Prover.Names where

import Language.Fixpoint.Types

runAppSymbol, exprToBoolSym, arrowConName :: Symbol
arrowConName = "Arrow"
runAppSymbol = "runApp"
exprToBoolSym = "exprToBool"

arrowFTyCon = symbolFTycon $ dummyLoc arrowConName
