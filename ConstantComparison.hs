
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ConstantComparison where

import Prelude hiding ( pure, return )

import RTick
import ProofCombinators
import Lists
import Erasure

--
-- Proving a password comparisons function adheres to the
-- \"constant-time discipline\" using relational cost analysis.
--

data Bit = Zero | One deriving Eq

{-@ reflect comp @-}
{-@ comp
  :: xs:[Bit]
  -> { ys:[Bit] | length xs == length ys }
  -> { t:Tick Bool | tcost t == length xs }
@-}
comp :: [Bit] -> [Bit] -> Tick Bool
comp []       _        = return True
comp (x : xs) (y : ys) = pure (&& x == y) </> comp xs ys

{-@ prop
  :: p:[Bit]
  -> { u1:[Bit] | length u1 == length p }
  -> { u2:[Bit] | length u2 == length p }
  -> { tcost (comp p u1) == tcost (comp p u2) }
@-}
prop :: [Bit] -> [Bit] -> [Bit] -> Proof
prop p u1 u2 = (comp p u1 *** QED) ? (comp p u2 *** QED)

{-@ propRel
  :: p:[Bit]
  -> { u1:[Bit] | length u1 == length p }
  -> { u2:[Bit] | length u2 == length p }
  -> { tcost (comp p u1) == tcost (comp p u2) }
@-}
propRel :: [Bit] -> [Bit] -> [Bit] -> Proof
propRel [] _ _ = ()
propRel (_ : ps) (_: u1s) (_ : u2s) = propRel ps u1s u2s
