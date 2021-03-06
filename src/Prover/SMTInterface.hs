module Prover.SMTInterface where

import Language.Fixpoint.Smt.Interface 

import Language.Fixpoint.Types hiding (allowHO)
import Language.Fixpoint.Types.Config

makeContext :: FilePath -> [(Symbol, Sort)] -> IO Context 
makeContext = makeZ3Context (defConfig{allowHO = True })

checkValid :: Context -> [Expr] -> Expr -> IO Bool
checkValid me is q = checkValidWithContext me [] (pAnd is) q

assert :: Context -> Expr -> IO ()
assert =  smtAssert
