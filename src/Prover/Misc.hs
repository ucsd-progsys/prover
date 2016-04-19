module Prover.Misc where

import Data.List

powerset :: [a] -> [[a]]
powerset = sortBy (\l1 l2 -> compare (length l1) (length l2)) . powerset'

powerset'       :: [a] -> [[a]]
powerset' []     = [[]]
powerset' (x:xs) = xss /\/ map (x:) xss
   where xss = powerset' xs

(/\/)        :: [a] -> [a] -> [a]
[]     /\/ ys = ys
(x:xs) /\/ ys = x : (ys /\/ xs)


findM :: (Monad m) => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ []     = return Nothing 
findM p (x:xs) = do {r <- p x; if r then return (Just x) else findM p xs}

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (x, y) = (x, f y)

second3 :: (b -> d) -> (a, b, c) -> (a, b, d) 
second3 f (x, y, z) = (x, f y, z)
