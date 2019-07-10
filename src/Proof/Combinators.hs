module Proof.Combinators where 

type Proof = ()
data QED   = QED

{-@ assert :: b:{Bool | b } -> {b} @-} 
assert :: Bool -> () 
assert _ = ()

{-@ (==.) :: x:a -> { y:a | x == y } -> { v:a | x == v && y == v } @-}
infixl 3 ==.
(==.) :: a -> a -> a
_ ==. x = x
{-# INLINE (==.) #-}



{-@ (***) :: a -> QED -> Proof  @-}
infixl 1 ***
(***) :: a -> QED -> Proof
_ *** _ = ()
{-# INLINE (***) #-}

{-@ (?) :: x:a -> Proof -> { v:a | x == v } @-}
infixl 3 ?
(?) :: a -> Proof -> a
x ? _ = x
{-# INLINE (?) #-}