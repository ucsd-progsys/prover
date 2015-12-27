module Prover.Defunctionalize where

import Prover.Names 
import Language.Fixpoint.Types



applyArrow y ys = go $ reverse ys 
  where 
    go []     = error "Defunctinalize.applyArrow on []"
    go [x]    = EApp (dummyLoc runFunName) [EVar y, EVar x]
    go (x:xs) = EApp (dummyLoc runFunName) [go xs,  EVar x]


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
