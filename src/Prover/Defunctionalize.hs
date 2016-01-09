{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Prover.Defunctionalize where

import Prover.Names 
import Prover.Misc (mapSnd, second3) 
import Language.Fixpoint.Types

import Control.Arrow (second)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import Data.Hashable

class Defunctionalize a where
  defunc :: a -> a 


instance Defunctionalize Sort where
  defunc (FFunc i ss) | i == 0    = arrowsSort ss 
                      | otherwise = FFunc i $ [arrowsSort ss]
  defunc (FApp s1 s2) = FApp (defunc s1) (defunc s2)
  defunc s            = s 


instance Defunctionalize Expr where
  defunc (EApp f es)    = defuncEApp f es 
  defunc (ENeg e)       = ENeg $ defunc e 
  defunc (EBin o e1 e2) = EBin o (defunc e1) (defunc e2)
  defunc (EIte p e1 e2) = EIte (defunc p) (defunc e1) (defunc e2)
  defunc (ECst e s)     = ECst (defunc e) (defunc s)
  defunc (PAnd ps)       = PAnd (defunc <$> ps)
  defunc (POr  ps)       = POr  (defunc <$> ps)
  defunc (PNot p)        = PNot (defunc p)
  defunc (PImp p1 p2)    = PImp (defunc p1) (defunc p2)
  defunc (PIff p1 p2)    = PIff (defunc p1) (defunc p2)
  defunc (PAtom b e1 e2) = PAtom b (defunc e1) (defunc e2)
  defunc (PAll ss p)     = PAll (mapSnd defunc <$> ss) (defunc p)
  defunc (PExist ss p)   = PExist (mapSnd defunc <$> ss) (defunc p)
  defunc e              = e 


defuncEApp :: LocSymbol -> [Expr] -> Expr
defuncEApp f [] = EVar $ val f
defuncEApp f ys = applyArrow (EVar $ val f) ys 

applyArrow y ys = go $ reverse ys 
  where 
    go []     = error "Defunctionalize.applyArrow on []"
    go [x]    = EApp (dummyLoc runAppSymbol) [y, x]
    go (x:xs) = EApp (dummyLoc runAppSymbol) [go xs, x]



exprToBool :: Expr -> Expr 
exprToBool e =  EApp (dummyLoc exprToBoolSym) [e]

instance Defunctionalize Reft where
  defunc (Reft (s, p)) = Reft (s, defunc p)

instance Defunctionalize SortedReft where
  defunc rr = rr {sr_sort = defunc $ sr_sort rr, sr_reft = defunc $ sr_reft rr} 

instance (Defunctionalize a) =>  (Defunctionalize (M.HashMap k a)) where
  defunc m = M.map defunc m

instance (Defunctionalize a) => (Defunctionalize [a]) where
  defunc = map defunc

instance (Defunctionalize a, Eq a, Hashable a) =>  (Defunctionalize (S.HashSet a)) where
  defunc m = S.map defunc m 

instance Defunctionalize IBindEnv where
  defunc x = x 

instance (Defunctionalize a) => (Defunctionalize (SEnv a)) where
  defunc = mapSEnv defunc  


instance Defunctionalize BindEnv where
  defunc = mapBindEnv (second defunc)

instance Defunctionalize Qualifier where
  defunc q = q{ q_params = second defunc <$> q_params q
              , q_body   = defunc $ q_body q 
              }

instance (Defunctionalize a) => Defunctionalize (WfC a) where
  defunc wfc = wfc { wenv  = defunc $ wenv wfc 
                   , wrft  = second3 defunc $ wrft wfc  
                   , winfo = defunc $ winfo wfc  
                   } 
instance (Defunctionalize a) => (Defunctionalize (SubC a)) where
  defunc subc = mkSubC (defunc $ senv subc)
                       (defunc $ slhs subc)
                       (defunc $ srhs subc)
                       (sid  subc)
                       (stag subc)
                       (defunc $ sinfo subc)

instance (Defunctionalize (c a), Defunctionalize a) => Defunctionalize (GInfo c a) where
  defunc finfo = finfo { cm       = defunc $ cm finfo
                       , ws       = defunc $ ws finfo
                       , bs       = defunc $ bs finfo
                       , lits     = insertSEnv runAppSymbol  runAppSort     $ 
                                    insertSEnv exprToBoolSym exprToBoolSort $ defunc $ lits finfo
                       , quals    = defunc $ quals finfo
                       , bindInfo = defunc $ bindInfo finfo
                       }

-------------------------------------------------------------------------------
---------------------------- runFun  ------------------------------------------
-------------------------------------------------------------------------------

arrowTyCon :: FTycon 
arrowTyCon = symbolFTycon $ dummyLoc (symbol "Arrow")

runAppSort :: Sort
runAppSort = FFunc 2 [FApp (FApp (FTC arrowFTyCon) (FVar 0)) (FVar 1), FVar 0, FVar 1]


exprToBoolSort :: Sort
exprToBoolSort = FFunc 1 [FVar 0, boolSort]


-------------------------------------------------------------------------------
---------------------------- HELPERS ------------------------------------------
-------------------------------------------------------------------------------


arrowsSort []     = error "arrowSort on empty list"
arrowsSort [x]    = x 
arrowsSort (x:xs) = arrowSort x $ arrowsSort xs 

arrowSort sx s = FApp (FApp (FTC arrowFTyCon) sx) s

makeArrow []  = error "Defunctionalize.makeArrow on empty list" 
makeArrow [s] = s
makeArrow (s:ss) = arrowSort s $ makeArrow ss 

unArrow :: Sort -> [Sort]
unArrow (FApp (FApp (FTC c) sx) s) | c == arrowFTyCon
  = sx:unArrow s
unArrow (FFunc _ [s]) 
  = unArrow s
unArrow s 
  = [s] 

-- | Manipulationg Sorts 

resultSort :: Sort -> Sort 
resultSort (FFunc _ ss) 
  = last ss
resultSort (FApp (FApp (FTC c) _ ) s) 
  | c == arrowFTyCon  = resultSort s 
resultSort s             
   = s

argumentsortArrow :: Sort -> [Sort]
argumentsortArrow s = case unArrow s of {[] -> []; ss -> init ss}

argumentsort :: Sort -> [Sort]
argumentsort (FFunc _ ss) = init ss 
argumentsort s            = [s]
