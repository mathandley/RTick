{-@ LIQUID "--reflection" @-}
module Proof.Quantified where 

import Data.RTick

infixl 3 <=> 
{-@ (<=>) :: t1:Tick a 
          -> t2:{Tick a | tval t1 == tval t2 && tcost t2 == tcost t1} 
          -> {t:Tick a | t == t2 && tval t1 == tval t && tval t2 == tval t && tcost t == tcost t2 && tcost t2 == tcost t } @-}
(<=>) :: Tick a -> Tick a -> Tick a 
(<=>) _ x = x 


infixl 3 >==
{-@ (>==) :: t1:Tick a -> i:Int
          -> t2:{Tick a | tval t1 == tval t2 && tcost t1 == i + tcost t2} 
          -> {t:Tick a | t == t2 && tval t1 == tval t && tval t2 == tval t && 
                         tcost t1 == i + tcost t && tcost t == tcost t2 } @-}
(>==) :: Tick a -> Int -> Tick a -> Tick a 
(>==) _ _ x = x 

infixl 3 ==>
(==>) :: (a -> b) -> a -> b 
f ==> x = f x     


infixl 3 <==
{-@ (<==) :: t1:Tick a -> i:Int
          -> t2:{Tick a | tval t1 == tval t2 && i + tcost t1 ==  tcost t2} 
          -> {t:Tick a | t == t2 && tval t1 == tval t && tval t2 == tval t && 
                         i + tcost t1 == tcost t && tcost t == tcost t2 } @-}
(<==) :: Tick a -> Int -> Tick a -> Tick a 
(<==) _ _ x = x 

infixl 3 ==<
(==<) :: (a -> b) -> a -> b 
f ==< x = f x     