{-@ LIQUID "--reflection" @-}
module Data.Lists where 

import Prelude hiding (length)
{-@ infix   :   @-}

{-@ measure length @-}
{-@ length :: [a] -> Nat @-} 
length :: [a] -> Int 
length [] = 0 
length (x:xs) = 1 + length xs     

{-@ reflect cons @-}
{-@ cons :: x:a -> xs:[a] -> {z:[a] | z == x:xs && length z == length xs + 1} @-}
cons :: a -> [a] -> [a]
cons x xs = x:xs