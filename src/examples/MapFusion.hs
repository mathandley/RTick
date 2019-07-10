{-@ LIQUID "--reflection" @-}
{-  LIQUID "--ple"        @-}
module MapFusion where 

import Prelude hiding (mapM, Applicative (..), Monad (..), length)    
import Data.RTick 
import Data.Lists 
import Proof.Combinators 
import Proof.Quantified 
{-@ infix   >>= @-}
{-@ infix   >=> @-}
{-@ infix   :   @-}



{-@ reflect mapM @-}
mapM :: (a -> Tick b) -> [a] -> Tick [b]
{-@ mapM :: (a -> Tick b) -> xs:[a] -> Tick {os:[b] | length os == length xs} @-}
mapM f []     = pure [] 
mapM f (x:xs) = step 1 (liftA2 cons (f x) (mapM f xs))


mapFusion :: (a -> Tick b) -> (b -> Tick c) -> [a] -> () 
{-@ mapFusion :: f:(a -> Tick b) -> g:(b -> Tick c) -> xs:[a] 
              -> { (tval (mapM f xs >>= mapM g)  == tval (mapM (f >=> g) xs)) && 
                   (tcost (mapM f xs >>= mapM g) == length xs  + tcost (mapM (f >=> g) xs))
                 }
  @-}
mapFusion f g [] 
  =   mapM f [] >>= mapM g
  <=> pure []   >>= mapM g 
  <=> mapM g []
  <=> pure []    
  <=> mapM (f >=> g) [] 
  *** QED 
mapFusion f g (x:xs) 
  =   mapM f (x:xs) >>= mapM g
  <=> (step 1 (liftA2 cons (f x) (mapM f xs))) >>= mapM g
  >== 1 ==>    liftA2 cons (f x) (mapM f xs) >>= mapM g
  <=> Tick (cf + cfs) (fx `cons` fxs) >>= mapM g 
  >== cf + cfs ==>  
      pure (fx `cons` fxs) >>= mapM g
  <=> mapM g (fx:fxs) 
  <=> step 1 (liftA2 cons (g fx) (mapM g fxs))
  >== 1 ==> 
      liftA2 cons (g fx) (mapM g fxs)
  <== cfs ==< 
      liftA2 cons (g fx) (mapM f xs >>= mapM g)
      ? mapFusion f g xs
  >== length xs ==>  
      liftA2 cons (g fx) (mapM (f >=> g) xs)
  <== cf ==< 
       liftA2 cons ((f >=> g) x) (mapM (f >=> g) xs)
  <== 1 ==< 
      step 1 (liftA2 cons ((f >=> g) x) (mapM (f >=> g) xs))
  <=> mapM (f >=> g) (x:xs) 
  *** QED 
    where Tick cf fx   = f x 
          Tick cfs fxs = mapM f xs





