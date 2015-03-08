{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014-15 Edward Kmett, 2008-2009 Lennart Augustsson
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- |The "Traced" module provides a simple way of tracing expression evaluation.
-- A value of type @Traced a@ has both a value of type @a@ and an expression tree
-- that describes how the value was computed.
--
-- There are instances for the 'Traced' type for all numeric classes to make
-- it simple to trace numeric expressions.
--
-- The expression tree associated with a traced value is exactly that: a tree.
-- But evaluation of expressions in Haskell typically has sharing to avoid recomputation.
-- This sharing can be recovered by the (impure) 'reShare' function.
--
-- $examples
-----------------------------------------------------------------------------
module Debug.Traced
  ( Traced, traced, named, nameTraced
  , unknown, unTraced, tracedD
  , TracedD, unTracedD
  , Traceable
  , liftT, liftFun, Liftable
  , showAsExp, showAsExpFull
  , reShare, simplify
  , ifT, (%==), (%/=), (%<), (%<=), (%>), (%>=)
  , (%&&), (%||), tnot
  , TracedExp, tracedExp, namedExp
  ) where

import Data.Typeable (Typeable)
import Debug.Traced.Internal

-- Boolean operations

-- |Traced version of /if/.
ifT :: (Traceable a) => Traced Bool -> Traced a -> Traced a -> Traced a
ifT c t e = apply (unTraced $ if b then t else e) "ifT" Nonfix $
  tracedD c : if b then [tracedD t, none] else [none, tracedD e] where
    none = tracedD u
    u = unknown "..." `asTypeOf` t
    b = unTraced c

infix 4 %==, %/=, %<, %<=, %>, %>=
-- |Comparisons generating traced booleans.
(%==), (%/=) :: (Traceable a, Eq a) => Traced a -> Traced a -> Traced Bool
(%==) = binOp (==) ("==", Infix 4)
(%/=) = binOp (/=) ("/=", Infix 4)

(%<), (%<=), (%>), (%>=) :: (Traceable a, Ord a) => Traced a -> Traced a -> Traced Bool
(%<)  = binOp (<)  ("<",  Infix 4)
(%<=) = binOp (<=) ("<=", Infix 4)
(%>)  = binOp (>)  (">",  Infix 4)
(%>=) = binOp (>=) (">=", Infix 4)

infixr 3  %&&
infixr 2  %||
(%&&) :: Traced Bool -> Traced Bool -> Traced Bool
(%&&) = binOp (&&) ("&&", InfixR 3)
(%||) :: Traced Bool -> Traced Bool -> Traced Bool
(%||) = binOp (&&) ("||", InfixR 2)
tnot :: Traced Bool -> Traced Bool
tnot = unOp not "not"

-----------------------------------

-- |A wrapper for 'Traced' to show it with full details.
newtype TracedExp a = TracedExp (Traced a) deriving 
  ( Typeable, Eq, Ord, Num, Fractional, Integral
  , Enum, Real, RealFrac, Floating, RealFloat
  )

instance (Traceable a, Show a) => Show (TracedExp a) where
  show (TracedExp x) = showAsExpFull x

tracedExp :: (Traceable a) => a -> TracedExp a
tracedExp = TracedExp . traced

namedExp :: (Traceable a) => String -> a -> TracedExp a
namedExp s = TracedExp . named s

