{-# LANGUAGE OverloadedStrings #-}

module Prover.Names where

import Language.Fixpoint.Types

arrowConName, runFunName :: Symbol
arrowConName = "Arrow"
runFunName   = "runFun"

arrowFTyCon = symbolFTycon $ dummyLoc arrowConName
