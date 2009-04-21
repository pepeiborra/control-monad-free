{- |
  Naive Free monads suffer from a quadratic complexity,
  as explained in

  * Janis Voigtlander, /Asymptotic Improvement of Computations over Free Monads, MPC'08/

  The solution is to redefine the Free datatype in CPS,
  similar to what is done in difference lists to solve the problem on quadratic append
  for lists.
-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}

module Control.Monad.Free.Improve (
   C(..), rep, improve
  ) where

import Control.Monad
import Control.Monad.Free


newtype C mu a = C (forall b. (a -> mu b) -> mu b)

rep :: Monad mu => mu a -> C mu a
rep m = C (m >>=)

improve :: Monad mu => C mu a -> mu a
improve (C p) = p return

instance Functor (C mu) where
  fmap f (C m) = C (\h -> m (h.f))
--  fmap f (C m) = C (m . (.f))

instance Monad (C mu) where
  return a = C (\h -> h a)
  C p >>= k = C (\h -> p (\a -> case k a of C q -> q h))

instance Functor f => MonadFree f (C (Free f)) where
  wrap t = C (\h -> wrap (fmap (\(C p) -> p h) t))
  free   = rep . (fmap.fmap.fmap) rep . free . improve

instance MonadPlus mu => MonadPlus (C mu) where
    mzero       = rep mzero
    mplus p1 p2 = rep (mplus (improve p1) (improve p2))