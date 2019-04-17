module Util where

twice :: Applicative m => m a -> m (a, a)
twice f = (,) <$> f <*> f
