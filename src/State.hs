{-# LANGUAGE ScopedTypeVariables #-}

module State (prop_lists_sorted) where

import           Control.Monad
import           Control.Monad.Trans.Maybe (MaybeT)
import           Data.List                 (sort)

import           Hedgehog
import qualified Hedgehog.Gen              as Gen
import qualified Hedgehog.Range            as Range

import           Hedgehog.Internal.Gen     (GenT (..))
import qualified Hedgehog.Internal.Gen     as Internal.Gen
import           Hedgehog.Internal.Tree    (NodeT (..), TreeT (..))

splits :: [a] -> [([a], a, [a])]
splits []     = []
splits (x:xs) = ([], x, xs) : map (\(as, b, cs) -> (x : as, b, cs)) (splits xs)

interleaveNodeM :: forall m a. Monad m => [NodeT m a] -> NodeT m [a]
interleaveNodeM = go
  where
    go :: [NodeT m a] -> NodeT m [a]
    go ts = NodeT (map nodeValue ts) $ concat [
          [ TreeT $ return $ go (as ++ cs)
          | (as, _b, cs) <- splits ts
          ]
        , [ TreeT $ runTreeT b' >>= \b'' -> return $ go (as ++ [b''] ++ cs)
          | (as, b, cs) <- splits ts
          , b' <- nodeChildren b
          ]
        ]

interleaveListM :: Monad m => [TreeT m a] -> m (NodeT m [a])
interleaveListM ts = interleaveNodeM <$> mapM runTreeT ts

freezeTree :: Monad m => GenT m a -> GenT m (TreeT (MaybeT m) a)
freezeTree = Internal.Gen.mapGenT return

list :: forall m a. Monad m => Range Int -> GenT m a -> GenT m [a]
list len genA =
    Internal.Gen.mapGenT go $ do
      n <- Gen.integral_ len
      replicateM n (freezeTree genA)
  where
    -- TODO: Doesn't respect the minimum bound on the length
    go :: TreeT (MaybeT m) [TreeT (MaybeT m) a] -> TreeT (MaybeT m) [a]
    go (TreeT mt) = TreeT $ mt >>= interleaveListM . nodeValue

prop_lists_sorted :: Property
prop_lists_sorted = property $ do
    xs <- forAll $ list (Range.constant 0 5) (Gen.int (Range.constant 0 100))
    assert $ sort xs == xs
