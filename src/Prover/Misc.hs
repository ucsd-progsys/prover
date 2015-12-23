module Prover.Misc where

import Data.List

-------------------------------------------------------------------------------
-----------------------   Playing with lists    -------------------------------
-------------------------------------------------------------------------------

-- | Combinations 
-- | Edit to allow for partial application: stop once you find empty list
-- | combine [[e11, e12, e13, e14], [e21, e22, e23], [e31], [], ....]
-- |    = [[e11, e21, e31], [e11, e22, e31], [e11, e23, e31], 
-- |       [e12, e21, e31], [e12, e22, e31], [e12, e23, e31], 
-- |       [e13, e21, e31], [e13, e22, e31], [e13, e23, e31],
-- |       [e14, e21, e31], [e14, e22, e31], [e14, e23, e31]]

combine :: [[a]] -> [[a]]
combine []          = [[]]
combine ([]:_)      = [[]]
combine ([x]:es)    = [x:ys | ys <- combine es]
combine ((x:xs):es) = [x:ys | ys <- combine es] ++ combine (xs:es)

-- | Combinations 
-- | Edit to allow for partial application: stop once you find empty list
-- | combine1 [[e11, e12, e13, e14], [e21, e22, e23], [e31]]
-- |    = [[e11, e21, e31], [e11, e22, e31], [e11, e23, e31], 
-- |       [e12, e21, e31], [e12, e22, e31], [e12, e23, e31], 
-- |       [e13, e21, e31], [e13, e22, e31], [e13, e23, e31],
-- |       [e14, e21, e31], [e14, e22, e31], [e14, e23, e31]]

combine1 :: [[a]] -> [[a]]
combine1 []          = [[]]
combine1 ([]:_)      = []
combine1 ([x]:es)    = [x:ys | ys <- combine1 es]
combine1 ((x:xs):es) = [x:ys | ys <- combine1 es] ++ combine1 (xs:es)


-- | combine2 old new : every resulting list should have at least one new element 

combine2 :: (Eq a) => [[a]] -> [[a]] -> [[a]]
combine2 old new = combine1 (zipWith (++) old new) \\ combine1 old 

-- | Powerset 
powerset = sortBy (\l1 l2 -> compare (length l1) (length l2)) . powerset'

powerset'       :: [a] -> [[a]]
powerset' []     = [[]]
powerset' (x:xs) = xss /\/ map (x:) xss
   where xss = powerset' xs

(/\/)        :: [a] -> [a] -> [a]
[]     /\/ ys = ys
(x:xs) /\/ ys = x : (ys /\/ xs)




-------------------------------------------------------------------------------
-----------------------   Playing with monads   -------------------------------
-------------------------------------------------------------------------------

findM :: (Monad m) => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ []     = return Nothing 
findM p (x:xs) = do {r <- p x; if r then return (Just x) else findM p xs}