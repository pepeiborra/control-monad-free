{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

module Control.Monad.Free (
   module Control.Monad,
   MonadFree(..),
   Free(..),
   foldFree, foldFreeM,
   evalFree, mapFree,
   FreeT(..),
   foldFreeT, foldFreeT', mapFreeT,
   wrap, wrap', unwrap,
   mapMP
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Foldable
import Data.Monoid
import Data.Traversable as T
import Prelude hiding (abs)

class (Functor f, Monad m) => MonadFree f m where
    free :: m a -> m (Either a (f (m a)))
    jail :: f (m a) -> m a

instance Functor f => MonadFree f (Free f) where
    free = evalFree (Pure . Left) (Pure . Right)
    jail = Impure

data Free f a = Impure (f (Free f a)) | Pure a
deriving instance (Show a, Show (f(Free f a))) => Show (Free f a)

instance Functor f => Functor (Free f) where
    fmap f (Pure a)    = Pure   (f a)
    fmap f (Impure fa) = Impure (fmap (fmap f) fa)

instance (Functor f, Foldable f) => Foldable (Free f) where
    foldMap f (Pure a)    = f a
    foldMap f (Impure fa) = fold $ fmap (foldMap f) fa

instance Traversable f => Traversable (Free f) where
    traverse f (Pure a)   = Pure   <$> f a
    traverse f (Impure a) = Impure <$> traverse (traverse f) a

instance Functor f => Monad (Free f) where
    return          = Pure
    Pure a    >>= f = f a
    Impure fa >>= f = Impure (fmap (>>= f) fa)

evalFree :: (a -> b) -> (f(Free f a) -> b) -> Free f a -> b
evalFree p _ (Pure x)   = p x
evalFree _ i (Impure x) = i x

foldFree :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldFree pure _    (Pure   x) = pure x
foldFree pure imp  (Impure x) = imp (fmap (foldFree pure imp) x)

foldFreeM :: (Functor f, Traversable f, Monad m) => (a -> m b) -> (f b -> m b) -> Free f a -> m b
foldFreeM pure _    (Pure   x) = pure x
foldFreeM pure imp  (Impure x) = imp =<< T.mapM (foldFreeM pure imp) x

mapFree :: (Functor f, Functor g) => (forall a. f a -> g a) -> Free f a -> Free g a
mapFree eta (Pure a)   = Pure a
mapFree eta (Impure x) = Impure (fmap (mapFree eta) (eta x))

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

instance (Functor f) => MonadTrans (FreeT f) where
    lift = FreeT . liftM Left

liftFree :: (Functor f, Monad m) => (a -> Free f b) -> (a -> FreeT f m b)
liftFree f = wrap . f

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

unwrap :: (Traversable f, Monad m) => FreeT f m a -> m(Free f a)
unwrap = foldFreeT (return . Pure) (return . Impure)

wrap :: (Functor f, Monad m) => Free f a -> FreeT f m a
wrap  = FreeT . foldFree (return . Left) (return . Right . fmap FreeT)

wrap' :: (Functor f, Monad m) => m(Free f a) -> FreeT f m a
wrap' = FreeT . join . liftM unFreeT . liftM wrap

-- mapM for Parameterized monads

mapMP   :: (Traversable t, Monad m) => (a -> m b) -> t a -> m (t b)
mapMP f = unwrapMonadP . traverse (WrapMonadP . f)
newtype WrappedMonadP m a = WrapMonadP { unwrapMonadP :: m a }

instance Monad m => Functor (WrappedMonadP m) where fmap f (WrapMonadP v) = WrapMonadP (liftM f v)

instance Monad m => Applicative (WrappedMonadP m) where
        pure = WrapMonadP . return
        WrapMonadP f <*> WrapMonadP v = WrapMonadP (f `ap` v)
