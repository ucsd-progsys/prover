{-# LANGUAGE OverloadedStrings #-}

module Prover.Names where

import Language.Fixpoint.Types

runAppSymbol, runPAppSymbol, arrowConName :: Symbol
arrowConName = "Arrow"
runAppSymbol = "runApp"
runPAppSymbol = "runBoolApp"

arrowFTyCon = symbolFTycon $ dummyLoc arrowConName
