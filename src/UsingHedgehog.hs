{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UsingHedgehog where

import Control.Monad
import Control.Monad.IO.Class
import Data.Functor.Identity
import Data.IORef
import Data.Maybe (listToMaybe)
import Data.Tree

import Hedgehog
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Internal.Gen      as H
import qualified Hedgehog.Internal.Property as H
import qualified Hedgehog.Internal.Region   as H
import qualified Hedgehog.Internal.Report   as H
import qualified Hedgehog.Internal.Runner   as H
import qualified Hedgehog.Internal.Seed     as H.Seed
import qualified Hedgehog.Internal.Tree     as H.Tree
import qualified Hedgehog.Internal.Tree     as H (Tree(..), Node(..))
import qualified Hedgehog.Range             as Range

import Util

genR :: (Monad m, Integral a) => (a, a) -> GenT m a
genR (lo, hi) = Gen.shrink (\a -> [lo .. pred a]) $
                  Gen.integral_ (Range.constant lo hi)

genIntPair :: Monad m => GenT m (Int, Int)
genIntPair = twice $ genR (0, 10)

-- We can recover proper shrinking by defining our own
-- BUT note that due to integrated shrinking we can now not even depend anymore
-- on any shrinker for 'Int'; we have to define everything here.
-- We also lose the advantage of preservering invariants
-- The list generator is a nice example: pick a length, then genreate a list
-- of that length, but with a shrinker that can actually produce shorter lists
-- (but it's nice that we can define a dependent shrinker like that and actually
-- get shrinking)
genIntPair' :: Monad m => GenT m (Int, Int)
genIntPair' = Gen.shrink shrink genIntPair
  where
    shrink :: (Int, Int) -> [(Int, Int)]
    shrink (a, b) = concat [ [ (a', b ) | a' <- pred' a ]
                           , [ (a , b') | b' <- pred' b ]
                           , [ (a', b') | a' <- pred' a
                                        , b' <- pred' b ]
                           ]

    pred' :: Int -> [Int]
    pred' n = [0 .. pred n]

-- works just as well: the shrinking function gets called recursively
genIntPair'' :: Monad m => GenT m (Int, Int)
genIntPair'' = Gen.shrink shrink genIntPair
  where
    shrink :: (Int, Int) -> [(Int, Int)]
    shrink (a, b) = concat [ [ (a', b ) | a' <- pred' a ]
                           , [ (a , b') | b' <- pred' b ]
                           , [ (a', b') | a' <- pred' a
                                        , b' <- pred' b ]
                           ]

    pred' :: Int -> [Int]
    pred' 0 = []
    pred' n = [n - 1]

-- often not minimal
--
-- For example, might give counter example
--
-- (4, 0)
--
-- Check the tree for
--
-- > Gen.printTreeWith 0 (Seed 0 13) genIntPair
--
-- If we start with (4, 1), once we do not shrink the 4, we then do not
-- come back after we have shrunk the 1 to see if we need to shrunk the 4
-- again

example1 :: GenT IO (Int, Int) -> Property
example1 gen = property $ do
    (a, b) <- H.forAllT gen
    assert $ a < b

-- always minimal
--
-- starting from (2,3)
--     > recheck (Size 0) (Seed 1680454200611125916 4343919243077020989) <property>
example2 :: GenT IO (Int, Int) -> Property
example2 gen = property $ do
    (a, b) <- H.forAllT gen
    assert $ a > b

-- often not minimal
example3 :: GenT IO (Int, Int) -> Property
example3 gen = property $ do
    (a, b) <- H.forAllT gen
    assert $ a /= b

showSmallCounterexample :: (GenT IO (Int, Int) -> Property) -> IO ()
showSmallCounterexample example = do
    (testSeed, genSeed) <- findTestStartingWith isSmall genIntPair example
    void $ runTest (Just testSeed) genIntPair example
    putStrLn "Shrink tree:"
    showTree $ genTree genSeed genIntPair
  where
    isSmall :: (Int, Int) -> Bool
    isSmall (x, y) = (x == 3 && y <= 3) || (y == 3 && x <= 3)

{-------------------------------------------------------------------------------
  Hedgehog auxiliary
-------------------------------------------------------------------------------}

-- | Wrapper around 'findTestSuchThat' to search for a specific starting point
findTestStartingWith :: forall a.
                        (a -> Bool)
                     -> (forall m. Monad m => GenT m a)
                     -> (GenT IO a -> Property)
                     -> IO (Seed, Seed)
findTestStartingWith propA = findTestSuchThat propTree'
  where
    propTree' :: Tree (Maybe a) -> Bool
    propTree' (Node Nothing  _) = False
    propTree' (Node (Just a) _) = propA a

-- | Find a test with a shrink tree satisfying a particular propety
--
-- Returns the seed to run the test (for 'runTest'') and the seed for the tree.
findTestSuchThat :: (Tree (Maybe a) -> Bool)
                 -> (forall m. Monad m => GenT m a)
                 -> (GenT IO a -> Property)
                 -> IO (Seed, Seed)
findTestSuchThat propTree gen prop = go
  where
    go :: IO (Seed, Seed)
    go = do
        testSeed <- H.Seed.random
        (genSeed : _previousTests, report) <- runTest' (Just testSeed) gen prop
        case H.reportStatus report  of
          H.OK       -> go
          H.GaveUp   -> error "findTestSuchThat: gave up"
          H.Failed _ -> do
            if propTree (genTree genSeed gen)
              then return (testSeed, genSeed)
              else go

-- | Wrapper around 'runTest' that displays the result and returns the seeds
runTest :: Maybe Seed
        -> (forall m. Monad m => GenT m a)
        -> (GenT IO a -> Property)
        -> IO [Seed]
runTest mSeed gen prop = do
    (seeds, result) <- runTest' mSeed gen prop
    putStrLn =<< H.renderResult Nothing Nothing result
    return seeds

-- | Run a test
--
-- Returns the result and the seeds used for the generator
runTest' :: Maybe Seed
         -> (forall m. Monad m => GenT m a)
         -> (GenT IO a -> Property)
         -> IO ([Seed], H.Report H.Result)
runTest' mSeed gen prop = do
    seed    <- case mSeed of
                 Just seed -> return seed
                 Nothing   -> H.Seed.random
    tracker <- newGenTracker
    region  <- H.newEmptyRegion
    report  <- H.checkRegion region Nothing Nothing sizeUnused seed
                 (prop (trackGen tracker gen))
    seeds   <- readIORef tracker
    return (seeds, report)

-- | We ignore the size parameter for this test
sizeUnused :: Size
sizeUnused = 0

{-------------------------------------------------------------------------------
  Hedgehog auxiliary: track generators

  When Hedgehog is executing tests, the seed used to to run generators depends
  on the precise details of the test and the implementation of various monads
  in Hedgehog itself. It is occassionally useful to track these seeds so that
  we can display the corresponding shrink tree.
-------------------------------------------------------------------------------}

type GenTracker = IORef [Seed]

trackGen :: MonadIO m => GenTracker -> GenT m a -> GenT m a
trackGen ref H.GenT{..} = H.GenT $ \size seed -> do
    H.Tree $ do
      liftIO $ modifyIORef ref (seed :)
      H.Tree.runTree (unGen size seed)

newGenTracker :: IO GenTracker
newGenTracker = newIORef []

{-------------------------------------------------------------------------------
  Hedgehog auxiliary: shrink trees
-------------------------------------------------------------------------------}

findTreeWithRoot :: forall a. Gen a -> (a -> Bool) -> Maybe Seed
findTreeWithRoot gen p = findTreeSuchThat gen p'
  where
    p' :: Tree (Maybe a) -> Bool
    p' (Node Nothing  _) = False
    p' (Node (Just a) _) = p a

findTreeSuchThat :: Gen a -> (Tree (Maybe a) -> Bool) -> Maybe Seed
findTreeSuchThat gen p = listToMaybe $ filter p' (map (Seed 0) [0..])
  where
    p' :: Seed -> Bool
    p' seed = p (genTree seed gen)

genTree :: Seed -> Gen a -> Tree (Maybe a)
genTree seed = effectfreeTree
             . H.runDiscardEffect
             . H.runGenT sizeUnused seed

effectfreeTree :: H.Tree Identity a -> Tree a
effectfreeTree (H.Tree (Identity (H.Node a ts))) =
    Node a (map effectfreeTree ts)

showTree :: forall a. Show a => Tree (Maybe a) -> IO ()
showTree = putStrLn . drawTree . fmap render
  where
    render :: Maybe a -> String
    render Nothing  = "<discard>"
    render (Just x) = show x
