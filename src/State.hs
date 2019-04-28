{-# LANGUAGE ScopedTypeVariables #-}

module State (prop_lists_sorted) where

import Control.Monad
import Control.Monad.Trans.Maybe (MaybeT)
import Data.List (sort)

import Hedgehog
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

import Hedgehog.Internal.Gen (GenT(..))
import qualified Hedgehog.Internal.Gen as Internal.Gen
import Hedgehog.Internal.Tree (Tree(..), Node(..))

splits :: [a] -> [([a], a, [a])]
splits []     = []
splits (x:xs) = ([], x, xs) : map (\(as, b, cs) -> (x : as, b, cs)) (splits xs)

interleaveNodeM :: forall m a. Monad m => [Node m a] -> Node m [a]
interleaveNodeM = go
  where
    go :: [Node m a] -> Node m [a]
    go ts = Node (map nodeValue ts) $ concat [
          [ Tree $ return $ go (as ++ cs)
          | (as, _b, cs) <- splits ts
          ]
        , [ Tree $ runTree b' >>= \b'' -> return $ go (as ++ [b''] ++ cs)
          | (as, b, cs) <- splits ts
          , b' <- nodeChildren b
          ]
        ]

interleaveListM :: Monad m => [Tree m a] -> m (Node m [a])
interleaveListM ts = interleaveNodeM <$> mapM runTree ts

freezeTree :: Monad m => GenT m a -> GenT m (Tree (MaybeT m) a)
freezeTree = Internal.Gen.mapGenT return

list :: forall m a. Monad m => Range Int -> GenT m a -> GenT m [a]
list len genA =
    Internal.Gen.mapGenT go $ do
      n <- Gen.integral_ len
      replicateM n (freezeTree genA)
  where
    -- TODO: Doesn't respect the minimum bound on the length
    go :: Tree (MaybeT m) [Tree (MaybeT m) a] -> Tree (MaybeT m) [a]
    go (Tree mt) = Tree $ mt >>= interleaveListM . nodeValue

prop_lists_sorted :: Property
prop_lists_sorted = property $ do
    xs <- forAll $ list (Range.constant 0 5) (Gen.int (Range.constant 0 100))
    assert $ sort xs == xs
