{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Experiment with filter in Hedgehog
module Filter (example, example', example'', example''') where

import           Control.Monad
import           Control.Monad.Morph
import           Control.Monad.Trans.Maybe
import           Data.Functor.Identity

import           Hedgehog
import qualified Hedgehog.Gen              as Gen
import           Hedgehog.Internal.Gen     (mapGenT, runDiscardEffect, withGenT)
import qualified Hedgehog.Internal.Gen     as Gen.Internal
import           Hedgehog.Internal.Tree    (NodeT (..), Tree, TreeT (..))

example :: Gen Int
example = Gen.filter even (Gen.element [1..10])

example' :: Gen Int
example' = filter' even (Gen.element [1..10])

example'' :: Gen Int
example'' = filter'' even (Gen.element [1..10])

example''' :: Gen Int
example''' = filter''' even (Gen.element [1..10])

-- `ensure` does not skip elements in the shrink tree that don't satisfy
-- the predicate, and instead stops early. This may result in non-minimal
-- shrinks, but QuickCheck does the same.
filter' :: MonadGen m => (a -> Bool) -> m a -> m a
filter' p gen = Gen.Internal.ensure p $
                  join (snd <$> Gen.filter (p . fst) (Gen.freeze gen))

filter'' :: forall a. (a -> Bool) -> Gen a -> Gen a
filter'' p gen = withGenT (mapGenT (go . runDiscardEffect)) $
                   join (snd <$> Gen.filter (p . fst) (Gen.freeze gen))
  where
    go :: Maybe (Tree a) -> TreeT (MaybeT Identity) a
    go mt =
        case mt of
          Nothing ->
            TreeT $ MaybeT $ Identity $ Nothing
          -- Gen.filter guarantees that @x@ must satisfy @p@
          Just (TreeT (Identity (NodeT x xs))) ->
            hoist generalize $
              TreeT (Identity (NodeT x (concatMap (flattenTree p) xs)))

flattenTree :: (a -> Bool) -> Tree a -> [Tree a]
flattenTree p (TreeT (Identity (NodeT x xs)))
    | p x       = [TreeT (Identity (NodeT x xs'))]
    | otherwise = xs'
  where
    xs' = concatMap (flattenTree p) xs

-- Generalizion of 'filter'''
--
-- The trouble is that in order to only evaluate parts of the tree, this may
-- rearrange the tree, and that will mean we might end up with a tree which
-- is not strictly in "shrinking order" anymore
filter''' :: MonadGen m => (a -> Bool) -> m a -> m a
filter''' p gen = withGenT (mapGenT (bubbleUp p)) $
                   join (snd <$> Gen.filter (p . fst) (Gen.freeze gen))

-- | Find the first node in the tree that matches the predicate; any trees
-- that we skipped in the process will be reattached as children to that node
bubbleUp :: Monad m => (a -> Bool) -> TreeT (MaybeT m) a -> TreeT (MaybeT m) a
bubbleUp p t = TreeT $ do
    mRoot <- findSubtree p t
    case mRoot of
      Nothing ->
        mzero
      Just (NodeT a ts, newChildren) ->
        return $ NodeT a (map (bubbleUp p) (ts ++ newChildren))

-- | Find the first subtree whose root matches the predicate, returning all
-- the trees we didn't look at unevaluated.
findSubtree :: forall m a. Monad m
            => (a -> Bool) -> TreeT m a -> m (Maybe (NodeT m a, [TreeT m a]))
findSubtree p = \t -> go [t]
  where
    go :: [TreeT m a] -> m (Maybe (NodeT m a, [TreeT m a]))
    go []             = return Nothing
    go (TreeT t : ts) = do
        n@(NodeT a ts') <- t
        if p a then return $ Just (n, ts)
               else go (ts ++ ts')
