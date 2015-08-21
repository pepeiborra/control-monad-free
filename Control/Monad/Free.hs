{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
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
   foldFreeA, mapFreeA,
-- * Translate between Free monad and Free monad transformer computations
   trans, trans', untrans,liftFree
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Data.Foldable
import Data.Traversable as T
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Prelude.Extras

-- | This type class generalizes over encodings of Free Monads.
class (Functor f, Monad m) => MonadFree f m where
    free :: m a -> m (Either a (f (m a)))  -- ^ 'Opens' a computation and allows to observe the side effects
    wrap :: f (m a) -> m a                 -- ^  Wraps a side effect into a monadic computation

instance Functor f => MonadFree f (Free f) where
    free = evalFree (Pure . Left) (Pure . Right)
    wrap = Impure

data Free f a = Impure (f (Free f a)) | Pure a deriving (Generic, Typeable)

instance (Eq1 f) => Eq1 (Free f) where (==#) = (==)
instance (Eq a, Eq1 f) => Eq (Free f a) where
 Pure a == Pure b = a == b
 Impure a == Impure b = a ==# b
 _ == _ = False

instance Ord1 f => Ord1 (Free f) where compare1 = compare
instance (Ord a, Ord1 f) => Ord (Free f a) where
  compare Impure{} Pure{} = LT
  compare Pure{} Impure{} = GT
  compare (Pure   a) (Pure   b) = compare a b
  compare (Impure a) (Impure b) = compare1 a b

instance (Show a, Show1 f) => Show (Free f a) where
  showsPrec p (Pure   a) = showParen (p > 0) $ ("Pure "   ++) . showsPrec  11 a
  showsPrec p (Impure a) = showParen (p > 0) $ ("Impure " ++) . showsPrec1 11 a

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

instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure   f <*> x = fmap f x
  Impure f <*> x = Impure (fmap (<*> x) f)


isPure Pure{} = True; isPure _ = False
isImpure = not . isPure

foldFree :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldFree pure _    (Pure   x) = pure x
foldFree pure imp  (Impure x) = imp (fmap (foldFree pure imp) x)

foldFreeM :: (Traversable f, Monad m) => (a -> m b) -> (f b -> m b) -> Free f a -> m b
foldFreeM pure _    (Pure   x) = pure x
foldFreeM pure imp  (Impure x) = imp =<< T.mapM (foldFreeM pure imp) x

foldFreeA :: (Traversable f, Applicative m) => (a -> m b) -> m (f b -> b) -> Free f a -> m b
foldFreeA pure _    (Pure   x) = pure x
foldFreeA pure imp  (Impure x) = imp <*> traverse (foldFreeA pure imp) x

induce :: (Functor f, Monad m) => (forall a. f a -> m a) -> Free f a -> m a
induce f = foldFree return (join . f)

evalFree :: (a -> b) -> (f(Free f a) -> b) -> Free f a -> b
evalFree p _ (Pure x)   = p x
evalFree _ i (Impure x) = i x

mapFree :: (Functor f, Functor g) => (f (Free g a) -> g (Free g a)) -> Free f a -> Free g a
mapFree eta = foldFree Pure (Impure . eta)

mapFreeM  :: (Traversable f, Functor g, Monad m) => (f (Free g a) -> m(g (Free g a))) -> Free f a -> m(Free g a)
mapFreeM eta = foldFreeM (return . Pure) (liftM Impure . eta)

mapFreeA  :: (Traversable f, Functor g, Applicative m) =>
             m (f (Free g a) -> g (Free g a)) -> Free f a -> m(Free g a)
mapFreeA eta = foldFreeA (pure . Pure) (liftA (Impure .) eta)

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

instance (Functor f, Functor a, Monad a) => Applicative (FreeT f a) where
    pure = FreeT . return . Left
    (<*>) = ap

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

instance (Functor f, Monad m, MonadIO m) => MonadIO (FreeT f m) where
    liftIO = lift . liftIO

instance (Functor f, Monad m, MonadPlus m) => MonadPlus (FreeT f m) where
    mzero = lift mzero
    mplus a b = FreeT (mplus (unFreeT a) (unFreeT b))

instance (Functor f, Functor m, Monad m, MonadPlus m) => Alternative (FreeT f m) where
    empty = mzero
    (<|>) = mplus

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

trans :: MonadFree f m => Free f a -> m a
trans  = foldFree return wrap

trans' :: (Functor f, Monad m) => m(Free f a) -> FreeT f m a
trans' = FreeT . join . liftM unFreeT . liftM trans

liftFree :: (Functor f, Monad m) => (a -> Free f b) -> (a -> FreeT f m b)
liftFree f = trans . f
