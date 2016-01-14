{-# LANGUAGE OverloadedStrings #-}

module Prover.Names where

import Language.Fixpoint.Types

runAppSymbol, exprToBoolSym :: Symbol
runAppSymbol = "runApp"
exprToBoolSym = "exprToBool"

arrowFTyCon = symbolFTycon $ dummyLoc arrowConName
