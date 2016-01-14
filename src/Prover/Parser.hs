module Prover.Parser where

import Prover.Types 
import Prover.Constants (default_depth)

import Text.Parsec

import Language.Fixpoint.Parse hiding (bindP)
import Language.Fixpoint.Types        ( Env, ofBexpr
                                      , SExpr(PAnd), symbol, Sort(FObj)
                                      , val, dummyLoc)

parseQuery :: String -> IO LQuery
parseQuery fn = parseFromFile (queryP fn) fn 


queryP fn = do
  n      <- depthP
  bs     <- sepBy envP   whiteSpace -- constants 
  semi
  vars   <- sepBy bindP  whiteSpace -- variables 
  semi
  let env = [(dummyLoc $ var_name v, var_sort v) | v <- bs ++ vars]
  ds     <- declsP env 
  axioms <- sepBy (axiomP env) whiteSpace -- axioms use the two above 
  semi
  ctors  <- sepBy (ctorP env)  whiteSpace
  semi 
  let env' = env ++ [(dummyLoc $ var_name $ vctor_var c, var_sort $ vctor_var c) | c <- ctors]
  goal   <- goalP env'
  return $ mempty { q_axioms = axioms
                  , q_vars   = vars
                  , q_ctors  = ctors
                  , q_goal   = goal
                  , q_fname  = fn
                  , q_depth  = n 
                  , q_env    = bs
                  , q_decls  = ds
                  }


declsP :: Env -> Parser [Predicate]
declsP env 
  = try (do {n <- sepBy (declP env) whiteSpace; semi; return n} )
  <|> return []

declP :: Env -> Parser Predicate
declP env = reserved "declare" >> predicateP env 

depthP :: Parser Int 
depthP = try (do {reserved "depth"; reserved "="; n <- fromInteger <$> integer; semi; return n} )
      <|> return default_depth

goalP :: Env -> Parser Predicate
goalP env = reserved "goal" >> colon >> predicateP env 

ctorP :: Env -> Parser LVarCtor
ctorP env = do reserved "constructor"
               v <- varP
               (vs, p) <- try (ctorAxiomP env)
               return $ VarCtor v vs p

ctorAxiomP env
   =  do reserved "with"
         reserved "forall"
         aargs <- argumentsP
         abody <- predicateP env 
         return (aargs, abody) 
  <|> return ([], Pred $ PAnd [])

bindP :: Parser LVar
bindP = reserved "bind" >> varP

envP :: Parser LVar
envP = reserved "constant" >> varP

predicateP      :: Env -> Parser Predicate
predicateP env  = Pred . ofBexpr env <$> predP

axiomP :: Env -> Parser LAxiom
axiomP env = do 
  reserved "axiom"
  aname <- mkVar . val  <$> symbolP
  colon
  reserved "forall"
  aargs <- argumentsP
  abody <- predicateP env 
  return $ Axiom aname aargs abody
 where
   dummySort = FObj (symbol "dummySort")
   mkVar x   = Var x dummySort ()


argumentsP :: Parser ([LVar])
argumentsP = brackets $ sepBy varP comma

varP :: Parser LVar
varP = do 
  x <- val <$> symbolP
  colon
  s <- sortP
  return $ Var x s ()



