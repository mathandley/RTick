{-@ LIQUID "--reflection" @-}
module Data.RTick where 

import Prelude hiding (Applicative (..), Monad(..))

data Tick a = Tick { tcost :: Int, tval :: a }
{-@ data Tick a = Tick { tcost :: Int, tval :: a } @-}

{-@ reflect pure @-}
pure :: a -> Tick a 
pure x = Tick 0 x 

{-@ reflect liftA2 @-}
liftA2 :: (a -> b -> c) -> Tick a -> Tick b -> Tick c 
liftA2 f (Tick i x) (Tick j y) = Tick (i+j) (f x y)

{-@ reflect >=> @-}
{-@ infixr   >=> @-}
(>=>) :: (a -> Tick b) -> (b -> Tick c) -> a -> Tick c 
(>=>) f g x = let Tick i y = f x in 
              let Tick j z = g y in Tick (i+j) z 
              
{-@ reflect >>= @-}
{-@ infix   >>= @-}
{-@ (>>=) :: mx:Tick a -> m:(a -> Tick b) -> {t:Tick b | tcost t == tcost mx + tcost (m (tval mx)) } @-}
(>>=) :: Tick a -> (a -> Tick b) -> Tick b 
Tick i x >>= m = let Tick j w = m x in Tick (i + j) w 

{-@ reflect bbind @-}
{-@ bbind :: n:Int -> mx:Tick a -> m:(a -> {t:Tick b | tcost t <= n }) 
          -> {t:Tick b | tcost t <= tcost mx + n } @-}
bbind :: Int -> Tick a -> (a -> Tick b) -> Tick b 
bbind _ (Tick i x) m = let Tick j w = m x in Tick (i + j) w 

{-@ reflect ebind @-}
{-@ ebind :: n:Int -> mx:Tick a -> m:(a -> {t:Tick b | tcost t == n }) 
          -> {t:Tick b | tcost t == tcost mx + n } @-}
ebind :: Int -> Tick a -> (a -> Tick b) -> Tick b 
ebind _ (Tick i x) m = let Tick j w = m x in Tick (i + j) w 




{-@ reflect step @-}
step :: Int -> Tick a -> Tick a 
step i (Tick j x) = Tick (i+j) x 