module Prover.Defunctionalize where

import Prover.Names 
import Prover.Misc (mapSnd) 
import Language.Fixpoint.Types



class Defunctinalize a where
  defunc :: a -> a 

instance Defunctinalize Sort where
  defunc (FFunc i ss) | i == 0    = arrowsSort ss 
                      | otherwise = FFunc i $ arrowsSort ss
  defunc (FApp s1 s2) = FApp (defunc s1) (defunc s2)
  defunc s            = s 


instance Defunctinalize Expr where
  defunc (EApp f es)    = defuncEApp f es 
  defunc (ENeg e)       = ENeg $ defunc e 
  defunc (EBin o e1 e2) = EBin o (defunc e1) (defunc e2)
  defunc (EIte p e1 e2) = EIte (defunc p) (defunc e1) (defunc e2)
  defunc (ECst e s)     = ECst (defunc e) (defunc s)
  defunc e              = e 


defuncEApp :: LocSymbol -> [Expr] -> Expr
defuncEApp f [] = EVar $ val f
defuncEApp f ys = go $ reverse (defunc <$> ys) 
  where 
    go []     = error ("Types.applyArrow on " ++ show (f, ys))
    go [x]    = F.EApp (F.dummyLoc runFunName) [EVar $ val f, x]
    go (x:xs) = F.EApp (F.dummyLoc runFunName) [go xs, x]

instance Defunctinalize Pred where
  defunc (PAnd ps)       = PAnd (defunc <$> ps)
  defunc (POr  ps)       = POr  (defunc <$> ps)
  defunc (PNot p)        = PNot (defunc p)
  defunc (PImp p1 p2)    = PImp (defunc p1) (defunc p2)
  defunc (PIff p1 p2)    = PIff (defunc p1) (defunc p2)
  defunc (PBexp e)       = PBexp (defunc e)
  defunc (PAtom b e1 e2) = PAtom b (defunc e1) (defunc e2)
  defunc (PAll ss p)     = PAll (mapSnd defunc <$> ss) (defunc p)
  defunc (PExist ss p)   = PExist (mapSnd defunc <$> ss) (defunc p)
  defunc p               = p

applyArrow y ys = go $ reverse ys 
  where 
    go []     = error "Defunctinalize.applyArrow on []"
    go [x]    = EApp (dummyLoc runFunName) [EVar y, EVar x]
    go (x:xs) = EApp (dummyLoc runFunName) [go xs,  EVar x]

arrowsSort []     = error "arrowSort on empty list"
arrowsSort [x]    = x 
arrowsSort (x:xs) = arrowSort x $ arrowsSort xs 

arrowSort sx s = FApp (FApp (FTC arrowFTyCon) sx) s

makeArrow []  = error "Defunctinalize.makeArrow on empty list" 
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
