{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FromScratch where

import Control.Monad
import Data.List (sort)
import Data.Tree
import qualified System.Random as R

import Util
import Debug.Trace

{-------------------------------------------------------------------------------
  Manual shrinking
-------------------------------------------------------------------------------}

newtype Gen a = Gen { runGen :: R.StdGen -> a }

instance Functor Gen where
  fmap = liftM

instance Applicative Gen where
  pure  = return
  (<*>) = ap

instance Monad Gen where
  return a = Gen $ \_prng -> a
  f >>= g  = Gen $ \ prng ->
               let (prng1, prng2) = R.split prng
               in runGen (g (runGen f prng1)) prng2

-- | Bundle generator and manually defined shrinker
--
-- NOTE: invariant (a appears in negative and positive position)
data ManualGen a = MG {
      gen    :: Gen a
    , shrink :: a -> [a]
    }

{-------------------------------------------------------------------------------
  Test-driver for manual shrinking
-------------------------------------------------------------------------------}

type Seed = Int

-- | Check that property holds for all generated values
mCheck :: Show a
       => ManualGen a  -- ^ Generator
       -> (a -> Bool)  -- ^ Property
       -> IO ()
mCheck gen p = do
    seed <- R.randomIO
    putStrLn $ "Using seed " ++ show seed
    mCheckWith seed gen p

mCheckWith :: Show a => Seed -> ManualGen a -> (a -> Bool) -> IO ()
mCheckWith seed gen p = do
    case mCounterExample seed gen p of
      Nothing -> putStrLn $ "OK"
      Just a  -> putStrLn $ "Counterexample: " ++ show a

-- | Find minimal counter-example (if one exists)
mCounterExample :: forall a. Seed -> ManualGen a -> (a -> Bool) -> Maybe a
mCounterExample seed MG{..} p = go (R.mkStdGen seed) numTests
  where
    numTests = 100

    go :: R.StdGen -> Int -> Maybe a
    go _    0 = Nothing
    go prng n = if not (p a)
                  then Just $ applyManualShrinker shrink p a
                  else go prng2 (n - 1)
      where
        (prng1, prng2) = R.split prng
        a = runGen gen prng1

-- | Apply manually defined shrinker to known-to-be-failing input
applyManualShrinker :: (a -> [a]) -> (a -> Bool) -> a -> a
applyManualShrinker f p a =
     case filter (not . p) (f a) of
       []   -> a
       a':_ -> applyManualShrinker f p a'

{-------------------------------------------------------------------------------
  Examples of generators with manually defined shrinkers
-------------------------------------------------------------------------------}

-- | Generate an element in the specified range, shrink to lower bound
-- Shrink maybe not optimal; orthogonal concern
mGenR :: (R.Random a, Enum a) => (a, a) -> ManualGen a
mGenR (lo, hi) = (mGenR_ (lo, hi)) {
      shrink = \a -> [a' | a' <- [lo .. pred a]]
    }

-- | Like 'mGenR', but don't shrink at all
mGenR_ :: (R.Random a, Enum a) => (a, a) -> ManualGen a
mGenR_ (lo, hi) = MG {
      gen    = Gen $ fst . R.randomR (lo, hi)
    , shrink = \_ -> []
    }

mGenPair :: ManualGen a -> ManualGen b -> ManualGen (a, b)
mGenPair genA genB = MG {
      gen    = (,) <$> gen genA <*> gen genB
    , shrink = \(a, b) -> concat [
                   [ (a', b ) | a' <- shrink genA a ]
                 , [ (a , b') | b' <- shrink genB b ]
                 , [ (a', b') | a' <- shrink genA a
                              , b' <- shrink genB b ]
                 ]
    }

{-------------------------------------------------------------------------------
  Example with manually defined shrinkers
-------------------------------------------------------------------------------}

mExample1 :: IO ()
mExample1 = mCheck mExampleIntPair (uncurry (<))

mExample2 :: IO ()
mExample2 = mCheck mExampleIntPair (uncurry (>))

-- Motivates the "parallel" shrinking case in mGenPair
mExample3 :: IO ()
mExample3  = mCheck mExampleIntPair (uncurry (/=))

mExampleInt :: ManualGen Int
mExampleInt = mGenR (0, 10)

mExampleIntPair :: ManualGen (Int, Int)
mExampleIntPair = mGenPair mExampleInt mExampleInt

{-------------------------------------------------------------------------------
  Integrated shrinking
-------------------------------------------------------------------------------}

newtype IntGen a = IG { genTree :: R.StdGen -> Tree a }

runIntGen :: Seed -> IntGen a -> Tree a
runIntGen seed IG{..} = genTree (R.mkStdGen seed)

instance Functor IntGen where
  fmap = liftM

instance Applicative IntGen where
  pure  = return
  (<*>) = ap

instance Monad IntGen where
  return a = IG $ \_prng -> Node a []
  f >>= g  = IG $ \ prng ->
               let (prng1, prng2) = R.split prng
               in bindTree (genTree f prng1) (\a -> genTree (g a) prng2)
    where
      -- 'Tree' has a 'Monad' instance but it flips the order of subtrees
      -- We define our own for closer compatibility with hedgehog
      bindTree :: Tree x -> (x -> Tree y) -> Tree y
      bindTree (Node x ts) h =
        let Node y ts' = h x
        in Node y $ map (flip bindTree h) ts ++ ts'

intGen :: ManualGen a -> IntGen a
intGen MG{..} = IG $ unfoldTree (\a -> (a, shrink a)) . runGen gen

iGenR :: (R.Random a, Enum a) => (a, a) -> IntGen a
iGenR = intGen . mGenR

iGenR_ :: (R.Random a, Enum a) => (a, a) -> IntGen a
iGenR_ = intGen . mGenR_

showTree :: Show a => Seed -> IntGen a -> IO ()
showTree seed gen = putStrLn $ drawTree $ show <$> runIntGen seed gen

{-------------------------------------------------------------------------------
  Looking for seeds (only useful for the blog post)
-------------------------------------------------------------------------------}

findTreeWithRoot :: forall a. (a -> Bool) -> IntGen a -> Seed
findTreeWithRoot p = findSeedSuchThat p'
  where
    p' :: Tree a -> Bool
    p' (Node a _) = p a

findSeedSuchThat :: (Tree a -> Bool) -> IntGen a -> Seed
findSeedSuchThat p gen = head $ filter p' ([0 ..])
  where
    p' :: Seed -> Bool
    p' seed = p (runIntGen seed gen)

{-------------------------------------------------------------------------------
  Test driver for integrated shrinking
-------------------------------------------------------------------------------}

iCheck :: Show a => IntGen a -> (a -> Bool) -> IO ()
iCheck gen p = do
    seed <- R.randomIO
    putStrLn $ "Using seed " ++ show seed
    iCheckWith seed gen p

iCheckWith :: Show a => Seed -> IntGen a -> (a -> Bool) -> IO ()
iCheckWith seed gen p =
    case iCounterExample seed gen p of
      Nothing -> putStrLn $ "OK"
      Just a  -> putStrLn $ "Counterexample: " ++ show a

iCounterExample :: forall a. Show a => Seed -> IntGen a -> (a -> Bool) -> Maybe a
iCounterExample seed IG{..} p = go (R.mkStdGen seed) numTests
  where
    numTests = 100

    go :: R.StdGen -> Int -> Maybe a
    go _    0 = Nothing
    go prng n = if not (p (rootLabel tree))
                  then trace ("root: " ++ show (rootLabel tree)) $
--                       trace ("tree: " ++ drawTree (fmap show tree)) $
                         Just $ applyIntegratedShrinker p tree
                  else go prng2 (n - 1)
      where
        (prng1, prng2) = R.split prng
        tree = genTree prng1

-- | Apply integrated shrinking to known-to-have-failed test result
applyIntegratedShrinker :: (a -> Bool) -> Tree a -> a
applyIntegratedShrinker p tree =
    case failed of
      []      -> rootLabel tree
      tree':_ -> applyIntegratedShrinker p tree'
  where
    failed = filter (not . p . rootLabel) (subForest tree)

{-------------------------------------------------------------------------------
  Examples of generators with integrated shrinking
-------------------------------------------------------------------------------}

-- try seed 11
exampleIntGenInt :: Seed -> IO ()
exampleIntGenInt seed = showTree seed $ iExampleInt

-- try seed 6
exampleIntGenPair :: Seed -> IO ()
exampleIntGenPair seed = showTree seed $ twice iExampleInt

iExample1 :: IO ()
iExample1 = iCheck iExampleIntPair (uncurry (<))

iExample2 :: IO ()
iExample2 = iCheck iExampleIntPair (uncurry (>))

iExample3 :: IO ()
iExample3  = iCheck iExampleIntPair (uncurry (/=))

iExampleInt :: IntGen Int
iExampleInt = intGen mExampleInt

iExampleIntPair :: IntGen (Int, Int)
iExampleIntPair = (,) <$> iExampleInt <*> iExampleInt

newtype Decreasing = Decreasing (Int, Int)
  deriving (Show)

iDecreasing :: IntGen Decreasing
iDecreasing = do
    x <- iExampleInt
    d <- iExampleInt
    return $ Decreasing (x, x - 1 - d)

{-------------------------------------------------------------------------------
  Overriding shrinking
-------------------------------------------------------------------------------}

overrideShrinker :: forall a. (a -> [a]) -> IntGen a -> IntGen a
overrideShrinker f IG{..} = IG $ override . genTree
  where
    override :: Tree a -> Tree a
    override (Node a _) = unfoldTree (\x -> (x, f x)) a

iExampleIntPair' :: IntGen (Int, Int)
iExampleIntPair' = overrideShrinker shrinkPair iExampleIntPair
  where
    shrinkPair :: (Int, Int) -> [(Int, Int)]
    shrinkPair (a, b) = concat [ [ (a', b ) | a' <- pred' a ]
                               , [ (a , b') | b' <- pred' b ]
                               , [ (a', b') | a' <- pred' a
                                            , b' <- pred' b ]
                               ]

    pred' :: Int -> [Int]
    pred' n = [0 .. pred n]

{-------------------------------------------------------------------------------
  Parallel shrinking
-------------------------------------------------------------------------------}

(<**>) :: IntGen (a -> b) -> IntGen a -> IntGen b
(<**>) genF genA = IG $ \prng ->
    let (prngF, prngA) = R.split prng
    in (uncurry ($)) <$> shrinkTreePair (genTree genF prngF)
                                        (genTree genA prngA)

infixl 4 <**>

shrinkTreePair :: Tree a -> Tree b -> Tree (a, b)
shrinkTreePair l@(Node a ls) r@(Node b rs) =
    Node (a, b) $ concat [
        [shrinkTreePair l' r  | l' <- ls]
      , [shrinkTreePair l  r' | r' <- rs]
      ]

iExampleIntPair'' :: IntGen (Int, Int)
iExampleIntPair'' = (,) <$> iExampleInt <**> iExampleInt

{-------------------------------------------------------------------------------
  Lists: manual case
-------------------------------------------------------------------------------}

mGenList :: ManualGen a -> ManualGen [a]
mGenList genA = MG{
      gen = do
        n <- gen $ mGenR (0,3)
        replicateM n $ gen genA
    , shrink = \xs -> concat [
          -- Shrink one of the elements
          [ as ++ [b'] ++ cs
          | (as, b, cs) <- splits xs
          , b' <- shrink genA b
          ]
          -- Drop one of the elements
        , [ as ++ cs
          | (as, _b, cs) <- splits xs
          ]
        ]
    }

mGenIntList :: ManualGen [Int]
mGenIntList = mGenList mExampleInt

-- Always the (unique) minimal counter example [1,0]
mExample4 :: IO ()
mExample4 = mCheck mGenIntList (\xs -> xs == sort xs)

{-------------------------------------------------------------------------------
  Lists: integrated case
-------------------------------------------------------------------------------}

-- Much less demanding example. Shows that shrinking of the list length works
-- Starting from [2,8,10] we shrink the length to [2,8], [2]; then the element
-- to [1], and finally to [0]. Nice.
iExample4 :: IO ()
iExample4 = iCheck (iGenList1 iExampleInt) null

-- Sorting example is much more demanding of the shrinker
iExample5 :: (IntGen Int -> IntGen [Int]) -> IO ()
iExample5 genAs = iCheck (genAs iExampleInt) (\xs -> xs == sort xs)

-- Most obvious way to define the instance. Does not work very well.
--
-- Produced non-minimal counter examples
--
-- For example, starting from [6,5] we cannot shrink the first element as
-- [5,5] is sorted; but once we start shrinking the second element we then
-- don't go back to shrink the first, and so we end up with
--
-- [6,0]
--
-- The same might also happen to the length of the list; after we start
-- shrinking the first element, we then won't go back to shrink the size
-- of the list.
iGenList1 :: IntGen a -> IntGen [a]
iGenList1 genA = do
    n <- iGenR (0, 3)
    replicateM n genA

-- | Generate fixed length list
iGenN :: Int -> IntGen a -> IntGen [a]
iGenN 0 _ = pure []
iGenN n g = (:) <$> g <**> iGenN (n - 1) g

-- Does much better, but for example starting from [2,8,2] will send up with
-- [0,1,0]: if we took a prefix, the list would be sorted [2,8], and once we
-- picked the length, we will not go back to fix the length again.
iGenList2 :: IntGen a -> IntGen [a]
iGenList2 genA = do
    n <- iGenR (0, 3)
    iGenN n genA

-- | Insert new subtrees after the existing ones
expand :: forall a. (a -> [a]) -> IntGen a -> IntGen a
expand shrinkMore IG{..} = IG $ go . genTree
  where
    go :: Tree a -> Tree a
    go (Node a ts) = Node a (map go ts ++ subForest (unfoldTree step a))

    step :: a -> (a, [a])
    step x = (x, shrinkMore x)

iGenList3 :: IntGen a -> IntGen [a]
iGenList3 genA =
    expand dropElement $ do
      n <- iGenR (0, 3)
      iGenN n genA

freeze :: IntGen a -> IntGen (IntGen a)
freeze IG{..} = IG $ \prng -> Node (IG $ \_ -> (genTree prng)) []

iGenList4' :: IntGen a -> IntGen [IntGen a]
iGenList4' genA =
     expand dropElement $ do
       n <- iGenR (0, 3)
       replicateM n (freeze genA)

sequenceA' :: [IntGen a] -> IntGen [a]
sequenceA' []     = pure []
sequenceA' (g:gs) = (:) <$> g <**> sequenceA' gs

iGenList4 :: IntGen a -> IntGen [a]
iGenList4 genA = sequenceA' =<< iGenList4' genA

{-------------------------------------------------------------------------------
  Interleaving
-------------------------------------------------------------------------------}

freezeTree :: IntGen a -> IntGen (Tree a)
freezeTree IG{..} = IG $ \prng -> Node (genTree prng) []

iGenList5' :: IntGen a -> IntGen [Tree a]
iGenList5' genA = do
     n <- iGenR_ (0, 3)
     replicateM n (freezeTree genA)

interleave :: [Tree a] -> Tree [a]
interleave ts =
    Node (map rootLabel ts) $ concat [
        -- Shrink one of the elements
        [ interleave (as ++ [b'] ++ cs)
        | (as, b, cs) <- splits ts
        , b' <- subForest b
        ]
        -- Drop one of the elements
      , [ interleave (as ++ cs)
        | (as, _b, cs) <- splits ts
        ]
      ]

iGenList5 :: forall a. IntGen a -> IntGen [a]
iGenList5 genA = IG $ go . genTree (iGenList5' genA)
  where
    go :: Tree [Tree a] -> Tree [a]
    go (Node _ (_:_)) = error "iGenList5: impossible"
    go (Node ts [])   = interleave ts

{-------------------------------------------------------------------------------
  Second example of interleaving: BST
-------------------------------------------------------------------------------}

data BST a = Leaf a | Branch (BST a) (BST a)
  deriving (Show, Functor)

inorder :: BST a -> [a]
inorder (Leaf a)     = [a]
inorder (Branch l r) = inorder l ++ inorder r

iGenBST' :: forall a. IntGen a -> IntGen (BST (Tree a))
iGenBST' genA = go =<< iGenR_ (0, 10)
  where
    go :: Int -> IntGen (BST (Tree a))
    go 0 = Leaf <$> freezeTree genA
    go 1 = Leaf <$> freezeTree genA
    go n = Branch <$> go l <*> go r
      where
        l = n `div` 2
        r = n - l

reduceOne :: BST (Tree a) -> [BST (Tree a)]
reduceOne (Leaf a)     = map Leaf $ subForest a
reduceOne (Branch l r) = concat [
                             [Branch l' r  | l' <- reduceOne l]
                           , [Branch l  r' | r' <- reduceOne r]
                           ]

dropOne :: BST (Tree a) -> [BST (Tree a)]
dropOne (Leaf _)     = []
dropOne (Branch l r) = concat [
                           [l]
                         , [r]
                         , [Branch l' r  | l' <- dropOne l]
                         , [Branch l  r' | r' <- dropOne r]
                         ]

interleaveBST :: BST (Tree a) -> Tree (BST a)
interleaveBST ts =
    Node (fmap rootLabel ts) $ concat [
        map interleaveBST $ reduceOne ts
      , map interleaveBST $ dropOne   ts
      ]

iGenBST :: forall a. IntGen a -> IntGen (BST a)
iGenBST genA = IG $ go . genTree (iGenBST' genA)
  where
    go :: Tree (BST (Tree a)) -> Tree (BST a)
    go (Node _ (_:_)) = error "iGenBST: impossible"
    go (Node ts [])   = interleaveBST ts

iExampleBST :: IO ()
iExampleBST = iCheck (iGenBST iExampleInt) (\t -> sort (inorder t) == inorder t)
