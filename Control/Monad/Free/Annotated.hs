{-# LANGUAGE OverlappingInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE CPP                    #-}

module Control.Monad.Free.Annotated
(
 Free(..),
 pure, impure,
 isPure, isImpure,
 down, up, ann,
 foldFree, foldFreeM,
 mapFree, mapFreeM,
 evalFree,
 fmap, unsafeFmap,
 mapM, unsafeMapM,
 join, unsafeJoin,
 traverse, unsafeTraverse,
 bind, unsafeBind,
 zipFree, zipFree_,
 Measured(..),
 mapMeasure, traverseMeasure,
 runMeasure
) where

-- -------------------------
-- * Annotated free monads
-- -------------------------
-- most of the code for annotated fixed points is extracted from Edward Kmett's :
-- http://comonad.com/reader/2009/incremental-folds/#more-83

import           Control.Applicative       hiding (pure)
import qualified Control.Applicative       as A
import           Control.DeepSeq
import           Control.Monad             (liftM, zipWithM_)
import           Control.Monad.Free        (MonadFree(..))
import qualified Control.Monad.Free        as Sans
#ifdef TRANSFORMERS
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.State -- (evalStateT, MonadState(..), lift)
#else
import           Control.Monad.State       (evalStateT, MonadState(..), lift)
#endif
import           Data.Either
import           Data.Foldable             as F
import           Data.Monoid
import           Data.Traversable          hiding (traverse,mapM)
import qualified Data.Traversable          as T
import           Prelude                   hiding (fmap, mapM)
import qualified Prelude                   as P

data Free ann f a = Impure ann (f(Free ann f a))
                  | Pure   ann a

ann (Impure ann _) = ann
ann (Pure   ann _) = ann
{-
instance (Functor f, Foldable f, Measured a ann) => MonadFree f (Free ann f) where
  free = evalFree (pure . Left) (pure . Right)
  wrap = impure
-}

instance (Eq a, Eq (f(Free ann f a))) => Eq (Free ann f a) where
  Impure _ a == Impure _ b = a == b
  Pure   _ a == Pure   _ b = a == b
  _          ==          _ = False

instance (Ord a, Ord (f(Free ann f a))) => Ord (Free ann f a) where
  compare (Impure _ a) (Impure _ b) = compare a b
  compare (Pure   _ a) (Pure   _ b) = compare a b
  compare Pure{} Impure{} = LT
  compare Impure{} Pure{} = GT

deriving instance (Show ann, Show a, Show (f(Free ann f a))) => Show (Free ann f a)

instance (Functor f, Foldable f) => Foldable (Free ann f) where
  foldMap f (Pure   _ a) = f a
  foldMap f (Impure _ a) = F.fold (P.fmap (foldMap f) a)

instance (NFData a, NFData (f(Free ann f a))) => NFData (Free ann f a) where
  rnf (Pure   _ a ) = rnf a `seq` ()
  rnf (Impure _ fa) = rnf fa `seq` ()

-- ** Measures
class Monoid v => Measured a v where measure :: a -> v
--instance Measured () () where measure = const ()
instance (Measured a ann, Functor f, Foldable f) =>  Measured (Free ann f a) ann where measure = measureFreeDefault

measureFreeDefault :: (Measured a ann, Functor f, Foldable f) =>
                      Free ann f a -> ann
measureFreeDefault = foldFree measure F.fold

instance (Measured a m) => Measured (Maybe a) m where
  measure Nothing  = mempty
  measure (Just x) = measure x

instance (Measured a ma, Measured b mb) => Measured (a,b) (ma,mb) where
  measure (a, b) = (measure a, measure b)

instance (Measured a ma, Measured b mb, Measured c mc) => Measured (a,b,c) (ma,mb,mc) where
  measure (a, b, c) = (measure a, measure b, measure c)

instance Measured a m => Measured [a] [m] where
  measure = map measure
{-
instance (Measured l ml, Measured r mr) => Measured (Either l r) (Either ml mr) where
  measure = either (Left . measure) (Right . measure)
-}

mapMeasure :: Functor f => (ann -> ann') -> Free ann f a -> Free ann' f a
mapMeasure f = go where
  go (Pure   ann a) = Pure   (f ann) a
  go (Impure ann t) = Impure (f ann) (go <$> t)

traverseMeasure :: (Traversable f, Applicative m) =>
                   (ann -> m ann') -> Free ann f a -> m (Free ann' f a)
traverseMeasure f = go where
  go (Pure ann a) = (`Pure` a) <$> f ann
  go (Impure ann t) = Impure <$> f ann <*> T.traverse go t

runMeasure :: (Traversable f, Applicative m) => Free (m ann) f a -> m (Free ann f a)
runMeasure = traverseMeasure id


-- ** Smart constructors
pure   ::  Measured a ann => a -> Free ann f a
impure :: (Monoid ann, Measured a ann, Functor f, Foldable f) => f(Free ann f a) -> Free ann f a

pure   x = Pure (measure x) x
impure f = Impure (foldMap measure f) f

isPure Pure{} = True
isPure _      = False

isImpure Impure{} = True
isImpure _        = False

-- ** Converting from/to unannotated form

down :: Functor f => Free ann f a -> Sans.Free f a
down = foldFree Sans.Pure Sans.Impure

up :: (Foldable f, Functor f, Monoid ann, Measured a ann) => Sans.Free f a -> Free ann f a
up = Sans.foldFree pure impure

-- ** Utilities

-- | Like 'P.fmap' but with a more constrained type

type Algebra    f a = f a -> a
type AlgebraM m f a = f a -> m a

-- | Catamorphism over a 'Free'
foldFree :: Functor f => (a->b) -> Algebra f b -> Free ann f a -> b
foldFree fp fi = loop where
  loop (Pure   _ x) = fp x
  loop (Impure _ x) = fi (P.fmap loop x)

-- | Effectful catamorphism over a 'Free'
foldFreeM :: (Monad m, Traversable f) => (a-> m b) -> AlgebraM m f b -> Free ann f a -> m b
foldFreeM fp fi = loop where
  loop (Pure   _ x) = fp x
  loop (Impure _ x) = fi =<< T.mapM loop x

mapFree :: (Monoid ann, Measured a ann, Functor f', Foldable f', Functor f) =>
           (forall a. f a -> f' a) -> Free ann f a -> Free ann f' a
mapFree eta = foldFree pure (impure . eta)

mapFreeM :: (Monoid ann, Measured a ann, Traversable f, Functor f', Foldable f', Monad m) =>
           (forall a. f a -> m(f' a)) -> Free ann f a -> m(Free ann f' a)
mapFreeM eta = foldFreeM (return.pure) (liftM impure . eta)

{-# INLINE evalFree #-}
evalFree :: (a -> b) -> (f(Free ann f a) -> b) -> Free ann f a -> b
evalFree p _ (Pure   _ x) = p x
evalFree _ i (Impure _ x) = i x

{-# INLINE fmap #-}
fmap :: (Functor f, Foldable f, Monoid ann, Measured b ann) => (a -> b) -> Free ann f a -> Free ann f b
fmap f = loop where
  loop (Pure   _ a) = pure (f a)
  loop (Impure _ a) = impure (P.fmap loop a)

{-# INLINE unsafeFmap #-}
-- | Like 'fmap' but with a more constrained type
unsafeFmap :: Functor f => (a -> b) -> Free ann f a -> Free ann f b
unsafeFmap f = loop where
  loop (Pure   h a) = Pure   h (f a)
  loop (Impure h a) = Impure h (P.fmap loop a)

{-# INLINE traverse #-}
-- | Like 'T.traverse' but with a more constrained type
traverse :: (Applicative m, Traversable f, Monoid ann, Measured b ann) => (a -> m b) -> Free ann f a -> m(Free ann f b)
traverse f = loop where
  loop (Pure   _ a) = pure   <$> f a
  loop (Impure _ a) = impure <$> T.traverse loop a

{-# INLINE unsafeTraverse #-}
-- | Like 'traverse' but safe only if the traversal preserves the measure
unsafeTraverse :: (Applicative m, Traversable f) => (a -> m b) -> Free ann f a -> m(Free ann f b)
unsafeTraverse f = loop where
  loop (Pure   h a) = Pure   h <$> f a
  loop (Impure h a) = Impure h <$> T.traverse loop a


{-# INLINE mapM #-}
-- | Like 'T.mapM' but with a more constrained type
mapM :: (Monad m, Traversable f, Monoid ann, Measured b ann) => (a -> m b) -> Free ann f a -> m(Free ann f b)
mapM f = unwrapMonad . traverse (WrapMonad . f)

{-# INLINE unsafeMapM #-}
unsafeMapM :: (Monad m, Traversable f) => (a -> m b) -> Free ann f a -> m(Free ann f b)
unsafeMapM f = unwrapMonad . unsafeTraverse (WrapMonad . f)

{-# INLINE bind #-}
-- | Like '(>>=)' but with a more restrictive type
bind :: (Functor f, Foldable f, Monoid ann, Measured b ann) =>
              (a -> Free ann f b) -> Free ann f a -> Free ann f b
bind f = loop where
  loop (Pure   _ a) = f a
  loop (Impure _ a) = impure (P.fmap loop a)

{-# INLINE unsafeBind #-}
-- | Like 'bind', but safe only if the monadic action preserves the measure
unsafeBind :: Functor f =>
              (a -> Free ann f b) -> Free ann f a -> Free ann f b
unsafeBind f = loop where
  loop (Pure   _ a) = f a
  loop (Impure h a) = Impure h (P.fmap loop a)

{-# INLINE join #-}
join :: (Functor f, Foldable f, Monoid ann, Measured v ann) =>
        Free ann f (Free ann f v) -> Free ann f v
join = bind id

{-# INLINE unsafeJoin #-}
unsafeJoin :: (Functor f, Foldable f, Monoid ann, Measured v ann) =>
        Free ann f (Free ann f v) -> Free ann f v
unsafeJoin = unsafeBind id

-- zipping annotated Free Monads

zipFree :: (Traversable f, Eq (f ()), Monad m, Monoid ann, Measured c ann) =>
           (Free ann f a -> Free ann f b -> m (Free ann f c))
         -> Free ann f a -> Free ann f b -> m (Free ann f c)
zipFree f m1@(Impure _ a) m2@(Impure _ b)
      | P.fmap (const ()) a == P.fmap (const ()) b = impure `liftM` unsafeZipWithG f a b
zipFree _ _ _ = fail "zipFree: structure mistmatch"

zipFree_ :: (Traversable f, Eq (f ()), Monad m) =>
            (Free ann f a -> Free ann f b -> m ()) -> Free ann f a -> Free ann f b -> m ()
zipFree_ f m1@(Impure _ a) m2@(Impure _ b)
      | P.fmap (const ()) a == P.fmap (const ()) b = zipWithM_ f (toList a) (toList b)
zipFree_ _ _ _ = fail "zipFree_: structure mismatch"


unsafeZipWithG :: (Traversable t1, Traversable t2, Monad m) => (a -> b -> m c) ->  t1 a -> t2 b -> m(t2 c)
unsafeZipWithG f t1 t2  = evalStateT (T.mapM zipG' t2) (toList t1)
       where zipG' y = do (x:xx) <- get
                          put xx
                          lift (f x y)