{-@ LIQUID "--reflection" @-}

module Foldl where

import Prelude hiding (foldl, foldl', Applicative (..), Monad (..), length, flip)
import Data.RTick 
import Data.Lists 
import Proof.Combinators 
import Proof.Quantified 





prop :: (b -> a -> Tick b) -> b -> [a] -> () 
{-@ prop :: f:(b -> a -> Tick b) -> z:b -> xs:[a] 
              -> { (tval (foldlM f z xs)  == tval (foldlM' f z xs)) && 
                   (tcost (foldlM f z xs) == length xs  + tcost (foldlM' f z xs))
                 }
         / [length xs] @-}
prop f z []
  =   foldlM f z []
  <=> pure z 
  <=> foldlM' f z [] 
  *** QED 
prop f z (x:xs)
  =   foldlM f z (x:xs)
  <=> 1 `step` ((f z x) >>= (flip (foldlM f) xs)) 
  >== 1 ==> ((f z x) >>= (flip (foldlM f) xs))
  >== cf ==> ((flip (foldlM f) xs) fx)
  <=> foldlM f fx xs
      ? prop f fx xs 
  >== length xs ==> foldlM' f fx xs 
  <=> foldlM' f fx xs 
  <=> ((flip (foldlM' f) xs) fx)
  <== cf ==< (f z x >>= (flip (foldlM' f) xs))
  <=> (f z x >>= (flip (foldlM' f) xs))
  <=> foldlM' f z (x:xs)
  *** QED 
  where
    Tick cf fx = f z x 


{-@ reflect foldlM @-}
foldlM :: (b -> a -> Tick b) -> b -> [a] -> Tick b 
foldlM f z []     = pure z
foldlM f z (x:xs) = 1 `step` ((f z x) >>= (flip (foldlM f) xs))


{-@ reflect foldlM' @-}
foldlM' :: (b -> a -> Tick b) -> b -> [a] -> Tick b 
foldlM' f z []     = pure z
foldlM' f z (x:xs) = f z x >>= (flip (foldlM' f) xs)

{-@ reflect flip @-}
flip f x y = f y x 
