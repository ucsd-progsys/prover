{-# LANGUAGE PatternGuards #-}

module Prover.Solve where

import Prover.Types
import Prover.SMTInterface
import Prover.Pretty ()
import Prover.Constants 
import Prover.Defunctionalize

import Prover.Misc (findM, powerset, combine2, combine, combine1)

import Language.Fixpoint.Smt.Interface (Context)
import Language.Fixpoint.Misc 

-- import Language.Fixpoint.SortCheck
import qualified Language.Fixpoint.Types as F 

import Data.List  (nubBy, nub, groupBy)
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
     proof   <- iterativeSolve γ (q_depth q) cxt es (p_pred $ q_goal q) (q_axioms q)
     putStrLn $ ("\nProof = \n" ++ show proof)
     return proof
  where 
    sorts = makeSorts q
    es    = initExpressions (q_vars q) (q_ctors q) sorts 
    env   = traceShow "\nNUB ENV = \n" $ nub ([(var_name v, var_sort v) | v <- ((ctor_var <$> q_ctors q) ++ q_vars q)] ++ [(var_name v, var_sort v) | v <- q_env q])
    γ     = F.fromListSEnv $ [(x, F.trueSortedReft s) | (x,s) <- env]


iterativeSolve :: PrEnv -> Int -> Context -> [ArgExpr a] -> F.Pred -> [Axiom a] -> IO (Proof a)
iterativeSolve γ iter cxt es q axioms = go [] ((\e -> e{arg_exprs = []}) <$> es) 0 es
  where 
    go _  _      i _  | i == iter = return Invalid 
    go as old_es i es = do prf   <- findValid cxt is q   
                           if isJust prf 
                                then do putStrLn "Minimizing Solution"
                                        Proof <$> minimize cxt (fromJust prf) q
                                else makeExpressions γ cxt is es >>= mapM (assertExpressions cxt) >>=
                                     go is (zipWith appendExprs es old_es) (i+1) 
                        where 
                         is = concatMap (instantiate γ old_es es) axioms ++ as
                         appendExprs ae1 ae2 = ae1 { arg_exprs = (arg_exprs ae1) ++ (arg_exprs ae2)
                                                   , arg_ctors = (arg_ctors ae1) ++ (arg_ctors ae2) 
                                                   }



findValid :: Context -> [Instance a] -> F.Pred -> IO (Maybe [Instance a])
findValid cxt ps q 
  = (\b -> if b then Just ps else Nothing) <$> checkValid cxt (p_pred . inst_pred <$> ps) q

minimize :: Context -> [Instance a] -> F.Pred -> IO [Instance a]
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

bruteSearch :: Context -> [Instance a] -> F.Pred -> IO (Maybe [Instance a])
bruteSearch cxt ps q 
  = findM (\is -> checkValid cxt (p_pred . inst_pred <$> is) q) (powerset ps)

filterEquivalentExpressions :: PrEnv -> Context -> [Instance a] -> (ArgExpr a, ArgExpr a) -> IO (ArgExpr a)
filterEquivalentExpressions γ cxt is (aeold, aenew) 
  = do es <- filterM f (arg_exprs aenew)
       return $ aenew{arg_exprs = es}
  where 
    f e@(EApp c es) = not <$> checkValid cxt ((predCtor c (mkcheckExpr γ <$> es)):(p_pred . inst_pred <$> is))
                                     (F.POr [F.PAtom F.Eq (mkcheckExpr γ e) (mkcheckExpr γ e') | e' <- (arg_exprs aeold)])
    f e = not <$> checkValid cxt (p_pred . inst_pred <$> is) (F.POr [F.PAtom F.Eq (mkcheckExpr γ e) (mkcheckExpr γ e') | e' <- (arg_exprs aeold)])


assertExpressions :: Context -> ArgExpr a -> IO (ArgExpr a)
assertExpressions cxt ae = (mapM go $ arg_exprs ae) >> return ae 
  where
    go (EApp c es) 
      | length es == length (ctor_vars c)
      = do mapM go es 
           assert cxt $ predCtor c (mkExpr <$> es)
    go _    
      = return ()

predCtor c es 
  | length es /= length (ctor_vars c) && length (ctor_vars c) /= 0
  = F.PTrue
  | otherwise 
  = let su = F.mkSubst $ zip (var_name <$> ctor_vars c) es
    in F.subst su (p_pred $ ctor_prop c)

makeExpressions :: PrEnv -> Context -> [Instance a] -> [ArgExpr a] -> IO [ArgExpr a]
makeExpressions γ cxt is es 
  = mapM (filterEquivalentExpressions γ cxt is) newes
         
  where
    newes  = traceShow ("\nNewExpressions\n" ++ showDebug allnew es) 
       [ (ae, makeNewExpr γ ae allnew) |ae <- es] 
    allnew = catMaybes (go <$> (groupBy (\x1 x2 -> fst x1 `unifiable` fst x2) $ concatMap (instantiateCtor es) cs))
    go [] = Nothing 
    go ses = Just (ArgExpr { arg_sort  = fst $ head ses
                     , arg_exprs = snd <$> ses 
                     , arg_ctors = cs })


    cs = arg_ctors $ head es 

makeNewExpr γ ae allnew 
  = ae {arg_exprs = filter (checkExpr γ) $ concatMap arg_exprs (filter (\ae -> arg_sort ae `unifiable` arg_sort ae) allnew)}

showDebug nae oae
  = "\nOld Sorts\n" ++ show old ++ "\nNEW\n" ++ show (map (\s -> (s, (map (unifiable s) old))) new)
  where
    old = arg_sort <$> oae
    new = arg_sort <$> nae

{-
           [ArgExpr { arg_sort  = s 
                    , arg_exprs = concatMap (instantiateCtor es) cs
                    , arg_ctors = cs
                    } | ArgExpr s _ cs <- es]
-}

initExpressions :: [Var a] -> [Ctor a] -> [F.Sort] -> [ArgExpr a]
initExpressions vs ctors sorts 
  = [ArgExpr { arg_sort  = s
             , arg_exprs = EVar <$> filter (unifiable s . var_sort) vs
             , arg_ctors = ctors -- This optimization can not be done when we have higher order CTors filter (unifiable s . resultSort . ctor_sort) ctors
             } | s <- sorts]


instantiateCtor :: [ArgExpr a] -> Ctor a -> [(F.Sort, Expr a)]
-- real functions should not be partially applied
instantiateCtor aes ctor | F.FFunc _ (_:_:_) <- ctor_sort ctor
  = traceShow "instantiateCtor" (go (ctor_sort ctor) <$> combine1 ess) 
  where
    ess   = arg_exprs . head <$> ((\s' -> (filter (unifiable s' . arg_sort) aes)) <$> (argumentsort $ ctor_sort ctor))
    go s es = (resultSort s, EApp ctor es)
instantiateCtor aes ctor = (go (unArrow $ ctor_sort ctor) <$> combine ess) 
  where
    ess   = arg_exprs . head <$> ((\s' -> (filter (unifiable s' . arg_sort) aes)) <$> (argumentsortArrow $ ctor_sort ctor))
    go ss es = (makeArrow $ drop (length es) ss, EApp ctor es)


instantiate :: PrEnv -> [ArgExpr a] -> [ArgExpr a] -> Axiom a -> [Instance a]
instantiate γ oldses ses a = catMaybes (axiomInstance γ a <$> combine2 oess ess)
    where
        sorts = var_sort <$> axiom_vars a 
        ess   = arg_exprs . head <$> ((\s' -> (filter (unifiable s' . arg_sort) ses))    <$> sorts)
        oess  = arg_exprs . head <$> ((\s' -> (filter (unifiable s' . arg_sort) oldses)) <$> sorts)

axiomInstance :: PrEnv -> Axiom a -> [Expr a] -> Maybe (Instance a) 
axiomInstance γ a es 
  = case checkSortedReftFull γ $ p_pred pred of
     Nothing -> Just i 
     Just _ -> Nothing  
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
     csorts = concatMap argumentsortArrow (ctor_sort  <$> q_ctors q)



unifiable :: F.Sort -> F.Sort -> Bool
unifiable (F.FVar _)   (F.FVar _)     = True 
unifiable (F.FVar _)   (F.FObj _)     = True 
unifiable (F.FObj _)   (F.FVar _)     = True 
unifiable (F.FVar _)   _              = False 
unifiable _            (F.FVar _)     = False 
unifiable (F.FObj _)   (F.FObj _)     = True 
unifiable (F.FApp c s) (F.FApp c' s') = unifiable c c' && unifiable s s'
unifiable t1 t2 = isJust $ unify t1 t2


