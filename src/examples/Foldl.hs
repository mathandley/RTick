{-@ LIQUID "--reflection" @-}

module Foldl where

import Prelude hiding (foldl, foldl', Applicative (..), Monad (..), length)
import Data.RTick 
import Data.Lists 

{-@ foldl :: (b -> a -> b) -> b -> xs:[a] 
          -> {t:Tick b | tcost t == length xs } @-} 
foldl :: (b -> a -> b) -> b -> [a] -> Tick b 
foldl f z [] = pure z
foldl f z (x:xs) = let w = f z x in
                   1 `step` foldl f w xs


{-@ foldl' :: (b -> a -> b) -> b -> xs:[a] 
          -> {t:Tick b | tcost t == 0 } @-} 
foldl' :: (b -> a -> b) -> b -> [a] -> Tick b 
foldl' f z [] = pure z
foldl' f z (x:xs) = let w = f z x in
                     w `seq` foldl' f w xs


{-@ foldlT :: n:Int -> (b -> a -> {t:Tick b | tcost t <= n }) -> b -> xs:[a] 
           -> {t:Tick b | tcost t <= (1 + n) * (length xs)  } @-} 
foldlT :: Int -> (b -> a -> Tick b) -> b -> [a] -> Tick b 
foldlT _ f z []     = pure z
foldlT n f z (x:xs) = 1 `step` bbind ((1 + n) * (length xs)) (f z x) (\w ->  
                       foldlT n f w xs)


 {-@ foldlT' :: n:Int -> (b -> a -> {t:Tick b | tcost t <= n }) -> b -> xs:[a] 
           -> {t:Tick b | tcost t <= n * (length xs) } @-} 
foldlT' :: Int -> (b -> a -> Tick b) -> b -> [a] -> Tick b 
foldlT' _ f z []     = pure z
foldlT' n f z (x:xs) = bbind (n * (length xs)) (f z x) (\w ->  
                       foldlT' n f w xs)


