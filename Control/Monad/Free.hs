{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

module Control.Monad.Free (
   module Control.Monad,
-- * Free Monads
   MonadFree(..),
   Free(..), isPure, isImpure,
   foldFree,
   evalFree, mapFree, mapFreeM, mapFreeM',
-- * Monad Morphisms
   foldFreeM,
   induce,
-- * Free Monad Transformers
   FreeT(..),
   foldFreeT, foldFreeT', mapFreeT,
-- * Translate between Free monad and Free monad transformer computations
   trans, trans', untrans,liftFree
  ) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans.Class
import Data.Foldable
import Data.Monoid
import Data.Traversable as T
import Prelude hiding (abs)

-- | This type class generalizes over encodings of Free Monads.
class (Functor f, Monad m) => MonadFree f m where
    free :: m a -> m (Either a (f (m a)))  -- ^ 'Opens' a computation and allows to observe the side effects
    wrap :: f (m a) -> m a                 -- ^  Wraps a side effect into a monadic computation

instance Functor f => MonadFree f (Free f) where
    free = evalFree (Pure . Left) (Pure . Right)
    wrap = Impure

data Free f a = Impure (f (Free f a)) | Pure a
deriving instance (Eq a, Eq (f(Free f a))) => Eq (Free f a)
deriving instance (Ord a, Ord (f(Free f a))) => Ord (Free f a)
deriving instance (Show a, Show (f(Free f a))) => Show (Free f a)

instance Functor f => Functor (Free f) where
    fmap f     = foldFree (Pure . f) Impure

instance (Functor f, Foldable f) => Foldable (Free f) where
    foldMap f  = foldFree f fold

instance Traversable f => Traversable (Free f) where
    traverse f = foldFree (fmap Pure . f) (fmap Impure . sequenceA)

instance Functor f => Monad (Free f) where
    return     = Pure
    m >>= f    = foldFree f Impure m

instance (NFData a, NFData (f(Free f a))) => NFData (Free f a) where
    rnf (Pure a) = rnf a `seq` ()
    rnf (Impure fa) = rnf fa `seq` ()

isPure Pure{} = True; isPure _ = False
isImpure = not . isPure

foldFree :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldFree pure imp = evalFree pure (imp . fmap (foldFree pure imp))

foldFreeM :: (Traversable f, Monad m) => (a -> m b) -> (f b -> m b) -> Free f a -> m b
foldFreeM pure imp = foldFree pure ((imp =<<) . T.sequence)

induce :: (Functor f, Monad m) => (forall a. f a -> m a) -> Free f a -> m a
induce f = foldFree return (join . f)

evalFree :: (a -> b) -> (f(Free f a) -> b) -> Free f a -> b
evalFree p _ (Pure x)   = p x
evalFree _ i (Impure x) = i x

mapFree :: (Functor f, Functor g) => (f (Free g a) -> g (Free g a)) -> Free f a -> Free g a
mapFree eta = foldFree Pure (Impure . eta)

mapFreeM  :: (Traversable f, Functor g, Monad m) => (f (Free g a) -> m(g (Free g a))) -> Free f a -> m(Free g a)
mapFreeM eta = foldFreeM (return . Pure) (liftM Impure . eta)

mapFreeM' :: (Functor f, Traversable g, Monad m) => (forall a. f a -> m(g a)) -> Free f a -> m(Free g a)
mapFreeM' eta = foldFree (return . Pure)
                         (liftM Impure . join . liftM T.sequence . eta)

-- * Monad Transformer
--   (built upon Luke Palmer control-monad-free hackage package)
newtype FreeT f m a = FreeT { unFreeT :: m (Either a (f (FreeT f m a))) }

instance (Traversable m, Traversable f) => Foldable (FreeT f m) where foldMap = foldMapDefault
instance (Traversable m, Traversable f) => Traversable (FreeT f m) where
  traverse f (FreeT a) = FreeT <$> ( traverse f' a) where
      f' (Left  x) = Left  <$> f x
      f' (Right x) = Right <$> (traverse.traverse) f x

editEither l r = either (Left . l) (Right . r)
conj f = FreeT . f . unFreeT

instance (Functor f, Functor m) => Functor (FreeT f m) where
    fmap f = conj $ fmap (editEither f ((fmap.fmap) f))

instance (Functor f, Monad m) => Monad (FreeT f m) where
    return = FreeT . return . Left
    m >>= f = FreeT $ unFreeT m >>= \r ->
        case r of
             Left  x  -> unFreeT $ f x
             Right xc -> return . Right $ fmap (>>= f) xc

instance (Functor f, Monad m) => MonadFree f (FreeT f m) where
    wrap = FreeT . return . Right
    free = lift . unFreeT

instance (Functor f) => MonadTrans (FreeT f) where
    lift = FreeT . liftM Left

foldFreeT :: (Traversable f, Monad m) => (a -> m b) -> (f b -> m b) -> FreeT f m a -> m b
foldFreeT p i m = unFreeT m >>= \r ->
              case r of
                Left   x -> p x
                Right fx -> T.mapM (foldFreeT p i) fx >>= i


foldFreeT' :: (Traversable f, Monad m) => (a -> b) -> (f b -> b) -> FreeT f m a -> m b
foldFreeT' p i (FreeT m) = m >>= f where
         f (Left x)   = return (p x)
         f (Right fx) = i `liftM` T.mapM (foldFreeT' p i) fx


mapFreeT :: (Functor f, Functor m) => (forall a. m a -> m' a) -> FreeT f m a -> FreeT f m' a
mapFreeT f (FreeT m) = FreeT (f ((fmap.fmap.fmap) (mapFreeT f) m))


untrans :: (Traversable f, Monad m) => FreeT f m a -> m(Free f a)
untrans = foldFreeT (return . Pure) (return . Impure)

trans :: (Functor f, Monad m) => Free f a -> FreeT f m a
trans  = FreeT . foldFree (return . Left) (return . Right . fmap FreeT)

trans' :: (Functor f, Monad m) => m(Free f a) -> FreeT f m a
trans' = FreeT . join . liftM unFreeT . liftM trans

liftFree :: (Functor f, Monad m) => (a -> Free f b) -> (a -> FreeT f m b)
liftFree f = trans . f
