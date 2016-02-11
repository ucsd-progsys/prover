{-# LANGUAGE PatternGuards #-}

module Prover.Solve where

import Prover.Types
import Prover.SMTInterface
import Prover.Pretty ()
import Prover.Constants 
import Prover.Misc (findM, powerset)

import Language.Fixpoint.Smt.Interface (Context)
-- import Language.Fixpoint.Misc 
import qualified Language.Fixpoint.Types as F 

import Data.List  (nubBy, nub, permutations, isPrefixOf, partition)
import Data.Maybe (isJust, fromJust, catMaybes)

import System.IO

import Control.Monad (filterM)

import Language.Fixpoint.SortCheck
import Language.Fixpoint.Types.Refinements (SortedReft)

type PrEnv = F.SEnv SortedReft  

solve :: Query a -> IO (Proof a)
solve q = 
  do putStrLn $ "Solving Query\n" ++ show q
     cxt     <- makeContext (smtFile $ q_fname q) env
     mapM_ (assert cxt) (p_pred <$> q_decls q)
     proof   <- iterativeSolve γ (q_depth q) cxt (varCtorToCtor <$> q_ctors q) es (p_pred $ q_goal q) (q_axioms q)
     putStrLn $ ("\nProof = \n" ++ show proof)
     return proof
  where 
    es    = initExpressions $ filter notGHCVar vars
    env   = nub ([(var_name v, var_sort v) | v <- ((vctor_var <$> q_ctors q) ++ q_vars q), notGHCVar v ] ++ [(var_name v, var_sort v) | v <- q_env q])
    γ     = F.fromListSEnv $ [(x, F.trueSortedReft s) | (x,s) <- env]
    vars  = if q_isHO q then ((vctor_var <$> q_ctors q) ++ q_vars q) else q_vars q


notGHCVar v 
  = not $ isPrefixOf "GHC" (show v)

iterativeSolve :: PrEnv -> Int -> Context -> [Ctor a] -> [Expr a] -> F.Expr -> [Axiom a] -> IO (Proof a)
iterativeSolve γ iter cxt cts es q axioms = go is0 [] 0 es
  where 
    go _  _      i _  | i == iter = return Invalid 
    go as old_es i es = do prf   <- findValid cxt is q  
                           -- putStr ("Validity check with " ++ show is ++ " IS " ++ show prf) 
                           if isJust prf 
                                then do putStrLn "Minimizing Solution"
                                        Proof <$> minimize cxt (fromJust prf) q
                                else do es' <-  makeExpressions γ cxt is cts es 
                                        mapM_ (assertExpressions γ cxt) es'
                                        go is (es ++ old_es) (i+1) es' 
                        where 
                         is = concatMap (instantiate γ old_es es) asn ++ as
    (as0, asn) = partition (null . axiom_vars) axioms
    is0        = (\a -> Inst a [] (axiom_body a)) <$> as0 




findValid :: Context -> [Instance a] -> F.Expr -> IO (Maybe [Instance a])
findValid cxt ps q 
  = (\b -> if b then Just ps else Nothing) <$> checkValid cxt (p_pred . inst_pred <$> ps) q

minimize :: Context -> [Instance a] -> F.Expr -> IO [Instance a]
minimize cxt ps q | length ps < epsilon = fromJust <$> bruteSearch cxt ps q 
minimize cxt ps q = go 1 [] ps 
  where
    n = length ps `div` delta
    go _ acc [] = if (length acc < length ps) then minimize cxt acc q else fromJust <$> bruteSearch cxt acc q  
    go i acc is = do let (ps1, ps2) = splitAt n is 
                     let as = p_pred . inst_pred <$> (acc ++ ps2)
                     res <- checkValid cxt as q
                     let _msg = show i ++ " / " ++ show delta ++ "\n"
                     putStr "*" >> hFlush stdout
                     if res then go (i+1) acc          ps2 
                            else go (i+1) (acc ++ ps1) ps2 

bruteSearch :: Context -> [Instance a] -> F.Expr -> IO (Maybe [Instance a])
bruteSearch cxt ps q 
  = findM (\is -> checkValid cxt (p_pred . inst_pred <$> is) q) (powerset ps)

filterEquivalentExpressions :: PrEnv -> Context -> [Instance a] -> [Expr a] -> [Expr a] -> IO [Expr a]
filterEquivalentExpressions γ cxt is esold esnew 
  = filterM f esnew
  where 
    f e@(EApp c es) = not <$> checkValid cxt ((predCtor γ c (mkExpr <$> es)):(p_pred . inst_pred <$> is))
                                     (F.POr $ catMaybes $ (makeEq γ e <$> esold))
    f e = not <$> checkValid cxt (p_pred . inst_pred <$> is) (F.POr $ catMaybes $ (makeEq γ e <$> esold))

makeEq :: PrEnv -> Expr a -> Expr a -> Maybe (F.Expr)
makeEq γ e1 e2 = case (checkSortedReftFull γ p) of 
                   Nothing -> Just p 
                   Just _  -> Nothing 
              where
                p = F.PAtom F.Eq (mkExpr e1) (mkExpr e2) 


assertExpressions :: PrEnv -> Context -> Expr a -> IO ()
assertExpressions γ cxt e = go e 
  where
    go (EApp c es) 
      | length es == length (ctor_vars c)
      = do mapM go es 
           assert cxt $ predCtor γ c (mkExpr <$> es)
    go _    
      = return ()

predCtor γ c es 
  | length es /= length (ctor_vars c) && length (ctor_vars c) /= 0
  = F.PTrue 
  | otherwise 
  = case checkSortedReftFull γ p of
     Nothing -> p
     Just _  -> F.PTrue 
  where 
    su = F.mkSubst $ zip (var_name <$> ctor_vars c) es
    p  = F.subst su (p_pred $ ctor_prop c)

makeExpressions :: PrEnv -> Context -> [Instance a] -> [Ctor a] -> [Expr a] -> IO [Expr a]
makeExpressions γ cxt is cts es 
  = filterEquivalentExpressions γ cxt is es newes       
  where
    newes = filter (checkExpr γ) [EApp c ess | c <- cts, ess <- concatMap permutations $ makeArgumnetsExpr (arity c) es]

makeArgumnetsExpr n es = concatMap (`makeArgs` es) [1..n]

arity :: Ctor a -> Int
arity c 
  = case F.functionSort $ ctor_sort c of 
      Nothing -> 0 
      Just (_, ss, _) -> length ss 

initExpressions :: [Var a] -> [Expr a]
initExpressions = map EVar

instantiate :: PrEnv -> [Expr a] -> [Expr a] -> Axiom a -> [Instance a]
instantiate γ oldses ses a 
  = catMaybes (axiomInstance γ a <$> args)

  where
    args   = filter hasNew $ concatMap permutations $ makeArgs' n (concatMap (duplicateArgs n) (oldses ++ ses))
    hasNew = any (`elem` ses)
    n      = length $ axiom_vars a


makeArgs' n es 
  | length es < n = []
  | otherwise     = makeArgs n es  
-- NV TODO: allow multiple occurences of the same argument
duplicateArgs _ e = [e]

makeArgs :: Int -> [Expr a] -> [[Expr a]]
makeArgs 0 _      = [[]]
makeArgs n (x:xs) 
 | n == length (x:xs)
 = [x:xs] 
 | otherwise
 = ((x:)<$> makeArgs (n-1) xs) ++ makeArgs n xs
makeArgs n xs = error ("makeArgs for "  ++ show (n, xs))


axiomInstance :: PrEnv -> Axiom a -> [Expr a] -> Maybe (Instance a) 
axiomInstance γ a es 
  = case checkSortedReftFull γ $ p_pred pred of
     Nothing -> Just {-  traceShow "\n\n Add instance" -} i
     Just _e  -> {- traceShow (show e ++ "\n\n Reject instance " ++ show i ) -} Nothing 
  where 
    pred = F.subst (F.mkSubst $ zip (var_name <$> (axiom_vars a)) (mkExpr <$> es)) (axiom_body a)
    i    = Inst { inst_axiom = a
                , inst_args  = es
                , inst_pred  = pred
                }


checkExpr :: PrEnv -> Expr a -> Bool
checkExpr γ e = not $ isJust $ checkSortedReftFull γ $ mkExpr e 

mkcheckExpr :: PrEnv -> Expr a -> F.Expr
mkcheckExpr γ e 
  = case checkSortedReftFull γ e' of
      Nothing -> e'
      Just d -> error ("Unsorted expression\n" ++ show e ++ "\nExpr = \n" ++ show e' ++ "\nError\n" ++ show d)

  where e' = mkExpr e   


makeSorts :: Query a -> [F.Sort]
makeSorts q = nubBy unifiable (asorts ++ csorts)
  where 
     asorts = var_sort <$> (concatMap axiom_vars $ q_axioms q)
     csorts = concatMap argumentsort ((var_sort . vctor_var) <$> q_ctors q)
     argumentsort s = case F.functionSort s of {Nothing -> []; Just (_, ss, s) -> s:ss}



unifiable :: F.Sort -> F.Sort -> Bool
unifiable (F.FVar _)   (F.FVar _)     = True 
unifiable (F.FVar _)   (F.FObj _)     = True 
unifiable (F.FObj _)   (F.FVar _)     = True 
unifiable (F.FVar _)   _              = False 
unifiable _            (F.FVar _)     = False 
unifiable (F.FObj _)   (F.FObj _)     = True 
unifiable (F.FApp c s) (F.FApp c' s') = unifiable c c' && unifiable s s'
unifiable t1 t2 = isJust $ unify (const $ error "NV TODO: prover.Solve") t1 t2


