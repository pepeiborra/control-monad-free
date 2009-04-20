module Control.Monad.Free.Zip where

import Control.Monad.Free
import Control.Monad.State
import Data.Foldable
import Data.Traversable as T

zipFree :: (Traversable f, Eq (f ()), Monad m) => (a -> b -> m c) -> Free f a -> Free f b -> m (Free f c)
zipFree f (Pure a) (Pure b) = Pure `liftM` f a b
zipFree f m1@(Impure a) m2@(Impure b)
      | fmap (const ()) a == fmap (const ()) b = Impure `liftM` unsafeZipWithG (zipFree f) a b
zipFree _ _ _ = fail "zipFree: not the same structure"

zipFree_ :: (Traversable f, Eq (f ()), Monad m) => (a -> b -> m ()) -> Free f a -> Free f b -> m ()
zipFree_ f (Pure a) (Pure b) = f a b
zipFree_ f m1@(Impure a) m2@(Impure b)
      | fmap (const ()) a == fmap (const ()) b = zipWithM_ (zipFree_ f) (toList a) (toList b)
zipFree_ _ _ _ = fail "zipFree: not the same structure"


unsafeZipWithG :: (Traversable t1, Traversable t2, Monad m) => (a -> b -> m c) ->  t1 a -> t2 b -> m(t2 c)
unsafeZipWithG f t1 t2  = evalStateT (T.mapM zipG' t2) (toList t1)
       where zipG' y = do (x:xx) <- get
                          put xx
                          lift (f x y)