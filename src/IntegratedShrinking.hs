{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module IntegratedShrinking where

import Control.Monad hiding (join)
import Data.Maybe (mapMaybe, fromJust, listToMaybe)
import Data.List (sort)
import GHC.Stack
import qualified System.Random as R

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

pickOne :: [a] -> [([a], a, [a])]
pickOne []     = []
pickOne [x]    = [([], x, [])]
pickOne (x:xs) = ([], x, xs)
               : map (\(as, b, cs) -> (x:as, b, cs)) (pickOne xs)

repeatUntil :: forall m a. Monad m => m a -> (a -> Bool) -> m a
repeatUntil ma p = search
  where
    search :: m a
    search = ma >>= \a -> if p a then return a else search

{-------------------------------------------------------------------------------
  Manual shrinking

  We do not use a StateT-like style because we want to be able to generate
  infinite structures.
-------------------------------------------------------------------------------}

newtype Gen a = Gen { runGen :: R.StdGen -> a }
  deriving (Functor)

instance Applicative Gen where
  pure  = return
  (<*>) = ap

instance Monad Gen where
  return x = Gen $ \_prng -> x
  Gen x >>= f = Gen $ \prng ->
    let (prngX, prngF) = R.split prng
    in runGen (f (x prngX)) prngF

data Manual a = Manual {
      gen    :: Gen a
    , shrink :: a -> [a]
    }

{-------------------------------------------------------------------------------
  Examples of 'Manual' instances
-------------------------------------------------------------------------------}

-- | Generate random value in specified range
--
-- Shrinks using binary search to lower bound.
mRandomR :: (R.Random a, Integral a) => (a, a) -> Manual a
mRandomR (lo, hi) = Manual {
      gen    = Gen (fst . R.randomR (lo, hi))
    , shrink = \x -> filter (\x' -> lo <= x' && x' < x)
                            [lo + x `div` 2, x - 1]
    }

-- | Generate a pair of values
--
-- We do not attempt to shrink both elements at once. Although this could result
-- in better shrinks, it means that for n subterms we would consider @O(2^n)@
-- combinations of elements to shrink, which is too costly.
mPair :: Manual a -> Manual b -> Manual (a, b)
mPair genA genB = Manual {
      gen    = (,) <$> gen genA <*> gen genB
    , shrink = \(x, y) -> concat [
                   -- Shrink the left element
                   [ (x', y)
                   | x' <- shrink genA x
                   ]
                   -- Shrink the right element
                 , [ (x, y')
                   | y' <- shrink genB y
                   ]
                 ]
    }

mList :: Manual Int -> Manual a -> Manual [a]
mList genLen genA = Manual {
      gen    = do n <- gen genLen
                  replicateM n (gen genA)
    , shrink = \xs -> concat [
                   -- Drop an element
                   [ as ++ cs
                   | (as, _b, cs) <- pickOne xs
                   ]
                   -- Shrink an element
                 , [ as ++ [b'] ++ cs
                   | (as, b, cs) <- pickOne xs
                   , b' <- shrink genA b
                   ]
                 ]
    }

-- | Filter out elements that don't satisfy the predicate
--
-- May loop indefinitely.
mSuchThat :: forall a. Manual a -> (a -> Bool) -> Manual a
mSuchThat genA p = Manual {
      gen    = gen genA `repeatUntil` p
    , shrink = shrink'
    }
  where
    shrink' :: a -> [a]
    shrink' x = concatMap (\x' -> if p x' then [x']
                                          else shrink' x')
                          (shrink genA x)

-- | Variation on 'mSuchThat' that stops earlier
--
-- Unlike in 'mSuchThat', when a shrunk value does not satisfy the predicate
-- we do not look for any values further down the shrink tree. This is faster
-- but may result in poorer shrinks.
mSuchThat_ :: forall a. Manual a -> (a -> Bool) -> Manual a
mSuchThat_ genA p = Manual {
      gen    = gen genA `repeatUntil` p
    , shrink = filter p . shrink genA
    }

-- | Generate even number in the specified range
--
-- We use 'mSuchThat' rather than 'mSuchThat_' because the latter would result
-- in poor shrinks:
--
-- > shrink (mRandomR (0, 10)                  ) 10 == [5, 9]
-- > shrink (mRandomR (0, 10) `mSuchThat`  even) 10 == [2,4,4,8]
-- > shrink (mRandomR (0, 10) `mSuchThat_` even) 10 == []
mEven :: (Int, Int) -> Manual Int
mEven (lo, hi) = mRandomR (lo, hi) `mSuchThat` even

-- | Wrong version of 'mEven'
mEvenWRONG :: (Int, Int) -> Manual Int
mEvenWRONG (lo, hi) = mRandomR (lo, hi) `mSuchThat_` even

-- | Alternative definition of 'mEven'
--
-- Generate-then-test is always slower than generators of values that we /know/
-- must satisfy the predicate (this may or may not matter, depending on the
-- probability that a randomly generated value satisfies the predicate).
--
-- However, note that the logic for " evenness " now lives in both the generator
-- and in the shrinker, and we cannot really re-use any existing code.
-- Integrated shrinking has a better story here.
mEven' :: (Int, Int) -> Manual Int
mEven' (lo, hi) = Manual {
      gen    = (*2) <$> gen (mRandomR (lo, hi `div` 2))
    , shrink = \x -> filter (\x' -> even x' && lo <= x' && x' < x)
                            [ lo + x `div` 2 - 1
                            , lo + x `div` 2
                            , x - 2
                            ]
    }

{-------------------------------------------------------------------------------
  Trees
-------------------------------------------------------------------------------}

data Tree a = Node { root :: a , subtrees :: [Tree a] }
  deriving (Functor)

singleton :: a -> Tree a
singleton x = Node x []

unfoldTree :: forall a. (a -> [a]) -> a -> Tree a
unfoldTree f = go
  where
    go :: a -> Tree a
    go x = Node x $ map go (f x)

-- | Prune any subtrees whose root does not satisfy the predicate
filterTree_ :: forall a. (a -> Bool) -> Tree a -> Maybe (Tree a)
filterTree_ p = go
  where
    go :: Tree a -> Maybe (Tree a)
    go (Node x xs)
      | p x       = Just $ Node x (mapMaybe go xs)
      | otherwise = Nothing

-- | Remove any elements from the tree that do not satisfy the predicate
filterTree :: forall a. (a -> Bool) -> Tree a -> [Tree a]
filterTree p = go
  where
    go :: Tree a -> [Tree a]
    go (Node x xs)
      | p x       = [Node x (concatMap go xs)]
      | otherwise = concatMap go xs

{-------------------------------------------------------------------------------
  @(Tree, singleton, interleave)@ forms an applicative functor, with 'singleton'
  playing the role of 'pure' and 'interleave' playing the role of '(<*>)'.

  We have to satisfy the following three properties:

  > pure f <*> x    == f     <$> x
  > f <*> pure x    == ($ x) <$> f
  > g <*> (f <*> x) == ((.) <$> g <*> f) <*> x

  For comparison, for pure functions the same three properties boil down to

  > f x     == f x       (this property becomes trivial)
  > f x     == ($ x) f
  > g (f x) == (g . f) x

  ("Control.Applicative" states 4 rules instead; the accompanying Coq file
  shows that the above three properties are sufficient, though perhaps not
  necessary.)
-------------------------------------------------------------------------------}

interleave :: Tree (a -> b) -> Tree a -> Tree b
interleave l@(Node f ls) r@(Node x rs) =
    Node (f x) $ concat [
        [ interleave l' r  | l' <- ls ]
      , [ interleave l  r' | r' <- rs ]
      ]

{-------------------------------------------------------------------------------
  However, this is not the only possible applicative functor. For example,
  we can switch the order around whilst still preserving the same properties.
-------------------------------------------------------------------------------}

interleave' :: Tree (a -> b) -> Tree a -> Tree b
interleave' l@(Node f ls) r@(Node x rs) =
    Node (f x) $ concat [
        [ interleave' l  r' | r' <- rs ]
      , [ interleave' l' r  | l' <- ls ]
      ]

{-------------------------------------------------------------------------------
  @(Tree, singleton, join)@ forms a monad, with 'singleton' playing the
  role of 'return'.

  As for 'Applicative', this means we have to satisfy three properties:

  > join (return     t) == t
  > join (return <$> t) == t
  > join (join t)       == join (join <$> t)
-------------------------------------------------------------------------------}

join :: Tree (Tree a) -> Tree a
join (Node (Node x xs) xss) = Node x (xs ++ map join xss)

{-------------------------------------------------------------------------------
  Also as for 'Applicative', however, we can change the ordering of the
  subtrees whilst still preserving the same properties.

  (This also means 'Tree' has (at least) /four/ 'Applicative' instances.)
-------------------------------------------------------------------------------}

join' :: Tree (Tree a) -> Tree a
join' (Node (Node x xs) xss) = Node x (map join' xss ++ xs)

{-------------------------------------------------------------------------------
  Integrated shrinking
-------------------------------------------------------------------------------}

newtype Integrated a = Integrated (R.StdGen -> Tree a)
  deriving (Functor)

withPRNG :: R.StdGen -> Integrated a -> Tree a
withPRNG prng (Integrated f) = f prng

instance Applicative Integrated where
  pure x = Integrated $ \_prng -> singleton x
  Integrated f <*> Integrated x = Integrated $ \prng ->
    let (prngF, prngX) = R.split prng
    in interleave (f prngF) (x prngX)

newtype Dependent a = Dependent { independent :: Integrated a }
  deriving (Functor)

lift :: Integrated a -> Dependent a
lift = Dependent

instance Applicative Dependent where
  pure  = return
  (<*>) = ap

instance Monad Dependent where
  return x = Dependent . Integrated $ \_prng -> singleton x
  Dependent (Integrated x) >>= f = Dependent . Integrated $ \prng ->
    let (prngX, prngF) = R.split prng
    in join $ fmap (withPRNG prngF . independent . f) (x prngX)

{-------------------------------------------------------------------------------
  From 'Manual' to 'Integrated'
-------------------------------------------------------------------------------}

integrated :: Manual a -> Integrated a
integrated Manual{..} = Integrated $ unfoldTree shrink . runGen gen

{-------------------------------------------------------------------------------
  This is useful to define "primitive" integrated shrinkers
-------------------------------------------------------------------------------}

iRandomR :: (R.Random a, Integral a) => (a, a) -> Integrated a
iRandomR = integrated . mRandomR

{-------------------------------------------------------------------------------
  As long as we just need 'Applicative', defining composite integrated
  shrinkers is easy. Indeed, we don't really need to provide such combinators
  at all.
-------------------------------------------------------------------------------}

iPair :: Integrated a -> Integrated b -> Integrated (a, b)
iPair genA genB = (,) <$> genA <*> genB

-- | Generate list of fixed size
iListOfSize :: Int -> Integrated a -> Integrated [a]
iListOfSize 0 _    = pure []
iListOfSize n genA = (:) <$> genA <*> iListOfSize (n - 1) genA

{-------------------------------------------------------------------------------
  We make the monad interface unavailable by default, to avoid unfortunate
  definitions such as the following variation on iPair.
-------------------------------------------------------------------------------}

-- | Invalid variation on 'iPair'
--
-- Since this uses the monad interface instead of the applicative one, this
-- introduces an unwanted ordering between the two elements. This is why we
-- do not make the monad interface available by default.
iPairWRONG :: Integrated a -> Integrated b -> Integrated (a, b)
iPairWRONG genA genB = independent $ do
    a <- lift genA
    b <- lift genB
    return (a, b)

{-------------------------------------------------------------------------------
  Example: generating lists of random length

  When there are true dependencies between the generators, however, we need
  to be more careful. Simple example is lists: generating the elements of the
  list is dependent on the length we pick, and hence we /need/ the monadic
  interface. This means however that we define our own shrinking, or else
  the resulting shrinker will be very poor.
-------------------------------------------------------------------------------}

-- | Invalid generator for lists
--
-- Not only does this introduce strict ordering between the length of the list
-- and its elements, it also introduces unnecessary ordering between the
-- elements themselves.
--
-- The absence of the 'Monad' instance helps avoid such definitions.
iListWRONG :: Integrated Int -> Integrated a -> Integrated [a]
iListWRONG genLen genA = independent $ do
    n <- lift genLen
    replicateM n (lift genA)

-- | Another invalid generator for lists
--
-- Although this one is slightly better as the elements as now independent
-- from each other, we still introduce an unnecessary ordering between picking
-- the length of the list and the elements.
--
-- As before, the absence of the 'Monad' instance helps avoid this definition.
iListWRONG' :: Integrated Int -> Integrated a -> Integrated [a]
iListWRONG' genLen genA = independent $ do
    n <- lift genLen
    lift $ iListOfSize n genA

-- | Make the shrink tree explicitly available
--
-- This is very useful when we need to override shrinking.
--
-- See 'iList' for an example.
freeze :: Integrated a -> Dependent (Tree a)
freeze (Integrated f) = Dependent $ Integrated $ singleton . f

-- | Just keep the root of the shrink tree
dontShrink :: Integrated a -> Dependent a
dontShrink (Integrated f) = Dependent $ Integrated $ singleton . root . f

-- | Helper function for working with dependent generators
--
-- Note that while passing 'sequenceA' for the first argument is type correct,
-- it probably does not have the desired effect: it will shrink the elements of
-- @f@, but it will not shrink the structure of @f@ itself.
--
-- See 'iList' for an example.
dependent :: HasCallStack => (a -> Tree b) -> Dependent a -> Integrated b
dependent manualShrinker (Dependent (Integrated f)) = Integrated $ \prng ->
    case f prng of
      Node xs [] -> manualShrinker xs
      _otherwise -> error "dependent: invalid"

-- | Generate list of elements
--
-- Note the use of 'dontShrink': this establishes the invariant that
-- 'dependent' relies on.
iList :: Integrated Int -> Integrated a -> Integrated [a]
iList genLen genA = dependent interleaveList $ do
    n <- dontShrink genLen
    replicateM n (freeze genA)
  where
    interleaveList :: [Tree a] -> Tree [a]
    interleaveList ts =
        Node (map root ts) $ concat [
            -- Drop one of the elements altogether
            [ interleaveList (as ++ cs)
            | (as, _b, cs) <- pickOne ts
            ]
            -- Shrink one of the elements
          , [ interleaveList (as ++ [b'] ++ cs)
            | (as, b, cs)  <- pickOne ts
            , b'           <- subtrees b
            ]
          ]

{-------------------------------------------------------------------------------
  Example: counting
-------------------------------------------------------------------------------}

data Couple a = One a | Two a a
  deriving (Show)

couple :: [a] -> Couple a
couple []         = error "couple: too few element"
couple [a]        = One a
couple [a, b]     = Two a b
couple _otherwise = error "couple: too many elements"

-- | Generator for 'Count' in the same style as we did for lists
--
-- This demonstrates that the pattern scales to other datatypes.
iGenCouple :: forall a. Integrated a -> Integrated (Couple a)
iGenCouple genA = dependent interleaveCount $ do
    n <- dontShrink (iRandomR (1, 2))
    couple <$> replicateM n (freeze genA)
  where
    interleaveCount :: Couple (Tree a) -> Tree (Couple a)
    interleaveCount (One a)   = One <$> a
    interleaveCount (Two a b) =
        Node (Two (root a) (root b)) $ concat [
            -- Drop an element
            [ interleaveCount (One a) ]
          , [ interleaveCount (One b) ]
            -- Shrink an element
          , [ interleaveCount (Two a' b ) | a' <- subtrees a ]
          , [ interleaveCount (Two a  b') | b' <- subtrees b ]
          ]

-- | Variation on 'iGenCouple'
--
-- Here we can really benefit from integrated shrinking: we just reuse the
-- one for lists: the 'Couple' will shrink as the list does.
iGenCouple' :: Integrated a -> Integrated (Couple a)
iGenCouple' = fmap couple . iList (iRandomR (1, 2))

-- | Pair a 'Couple' with the list that generated it
data WrappedCouple a = WrappedCouple [a] (Couple a)

wrappedCouple :: [a] -> WrappedCouple a
wrappedCouple xs = WrappedCouple xs (couple xs)

-- | Attempt to define the equivalent of 'iGenCouple'' using manual shrinking
--
-- Note that this requires a wrapper type, and hence we lose compositionaly
-- (if we have other types that need 'Couple's as subterms, we cannot use
-- 'WrappedCouple'). An real-life example of this is QuickCheck's
-- 'Function' type.
mGenCouple' :: forall a. Manual a -> Manual (WrappedCouple a)
mGenCouple' genA = Manual {
      gen    = wrappedCouple <$> gen genAs
    , shrink = \(WrappedCouple xs _) -> map wrappedCouple (shrink genAs xs)
    }
  where
    genAs :: Manual [a]
    genAs = mList (mRandomR (1, 2)) genA

{-------------------------------------------------------------------------------
  Example: filtering
-------------------------------------------------------------------------------}

-- | Invalid definition of filtering
--
-- Note what would happen here: the check if the element satisfies the
-- predicate would be applied /at every value/ in the shrink tree, and whenever
-- it fails, the /entire/ process would be restarted (pick a new value,
-- validate it against the predicate, shrink it). This is clearly not what
-- we want. The absence of the 'Monad' instance for 'Integrated' helps avoid
-- such mistakes.
iSuchThatWRONG :: Integrated a -> (a -> Bool) -> Integrated a
iSuchThatWRONG genA p = independent $ lift genA `repeatUntil` p

-- | Filter out elements that do not satisfy the predicate
iSuchThat :: Integrated a -> (a -> Bool) -> Integrated a
iSuchThat genA p = dependent (filtered . filterTree p) $
    freeze genA `repeatUntil` (p . root)
  where
    -- Top-level result /must/ be a single tree since we know that the
    -- root of the tree must satisfy the predicate
    filtered :: [Tree a] -> Tree a
    filtered [x] = x
    filtered _   = error "iSuchThat: impossible"

-- | Faster version of 'iSuchThat'
--
-- This is a version of 'iSuchThat' that does not attempt to shrink a value that
-- does not satisfy the predicate any further. It trades shrinking performance
-- for the quality of the shrinks.
iSuchThat_ :: Integrated a -> (a -> Bool) -> Integrated a
iSuchThat_ genA p = dependent (fromJust . filterTree_ p) $
    freeze genA `repeatUntil` (p . root)

{-------------------------------------------------------------------------------
  Example: even numbers
-------------------------------------------------------------------------------}

-- | Produce an even number in the specified range
--
-- Note that the use of 'iSuchThat_' here would produce poor shrinks.
iEven :: (Int, Int) -> Integrated Int
iEven (lo, hi) = iRandomR (lo, hi) `iSuchThat` even

-- | Variation on 'iEven' using the wrong filter
iEvenWRONG :: (Int, Int) -> Integrated Int
iEvenWRONG (lo, hi) = iRandomR (lo, hi) `iSuchThat_` even

-- | Alternative definition of 'iEven'
--
-- This is a nice example where we can really benefit from integrated shrinking.
iEven' :: (Int, Int) -> Integrated Int
iEven' (lo, hi) = (*2) <$> iRandomR (lo, hi `div` 2)

{-------------------------------------------------------------------------------
  Driver
-------------------------------------------------------------------------------}

type Seed = Int

checkIntegrated :: Show a => Integrated a -> (a -> Bool) -> IO ()
checkIntegrated genA p = do
    seed <- R.randomIO
    putStrLn $ "Using seed " ++ show seed
    checkIntegratedWith seed genA p

checkIntegratedWith :: forall a. Show a
                    => Seed -> Integrated a -> (a -> Bool) -> IO ()
checkIntegratedWith seed genA p = do
    case findCounterexample p (root (withPRNG (R.mkStdGen seed) genAs)) of
      Nothing ->
        putStrLn $ "OK"
      Just (a, shrunk) -> do
        putStrLn $ "Failed: " ++ show a
        putStrLn $ "Shrunk: " ++ show shrunk
  where
    numTests :: Int
    numTests = 100

    genAs :: Integrated [Tree a]
    genAs = independent $ replicateM numTests (freeze genA)

-- | Find counter example to the specified property
--
-- If a counter-example was found, returns the counter-example as well as its
-- shrunk form.
--
-- NOTE: This hardcodes another point where we stop early, rather than
-- continue shrinking.
findCounterexample :: forall a. (a -> Bool) -> [Tree a] -> Maybe (a, a)
findCounterexample p =
      fmap (\x -> (root x, minimize x))
    . listToMaybe
    . filter (not . p . root)
  where
    minimize :: Tree a -> a
    minimize (Node x xs) =
        case filter (not . p . root) xs of
          []   -> x
          x':_ -> minimize x'

checkManual :: Show a => Manual a -> (a -> Bool) -> IO ()
checkManual = checkIntegrated . integrated

checkManualWith :: forall a. Show a
                => Seed -> Manual a -> (a -> Bool) -> IO ()
checkManualWith seed = checkIntegratedWith seed . integrated

{-------------------------------------------------------------------------------
  Example top-level calls
-------------------------------------------------------------------------------}

mExampleInt :: Manual Int
mExampleInt = mRandomR (0, 100)

iExampleInt :: Integrated Int
iExampleInt = iRandomR (0, 100)

-- | All numbers are even
--
-- This shows that we /still/ may not shrink all the way, because
-- 'findCounterexample' stops as soon as shrinking yields only values that
-- are not counter-examples anymore.
mExampleEven :: IO ()
mExampleEven = checkManual mExampleInt even

-- | All even numbers are less than 5
--
-- Note how 'mExampleEven5''' does not shrink properly.
mExampleEven5, mExampleEven5', mExampleEven5'' :: IO ()
mExampleEven5   = checkManual (mEven      (0, 100)) (< 5)
mExampleEven5'  = checkManual (mEven'     (0, 100)) (< 5)
mExampleEven5'' = checkManual (mEvenWRONG (0, 100)) (< 5)

-- | All even numbers are less than 5
--
-- As above, 'iExampleEven5''' shrinks poorly.
iExampleEven5, iExampleEven5', iExampleEven5'' :: IO ()
iExampleEven5   = checkIntegrated (iEven      (0, 100)) (< 5)
iExampleEven5'  = checkIntegrated (iEven'     (0, 100)) (< 5)
iExampleEven5'' = checkIntegrated (iEvenWRONG (0, 100)) (< 5)

-- | First element is always less than the second element of a pair
iExampleLess, iExampleLess' :: IO ()
iExampleLess  = checkIntegrated
                  (iPair iExampleInt iExampleInt)
                  (uncurry (<))
iExampleLess' = checkIntegrated
                  (iPairWRONG iExampleInt iExampleInt)
                  (uncurry (<))

-- | All lists are sorted
iExampleSorted, iExampleSorted', iExampleSorted'' :: IO ()
iExampleSorted   = checkIntegrated
                     (iList (iRandomR (0, 3)) iExampleInt)
                     (\xs -> xs == sort xs)
iExampleSorted'  = checkIntegrated
                     (iListWRONG (iRandomR (0, 3)) iExampleInt)
                     (\xs -> xs == sort xs)
iExampleSorted'' = checkIntegrated
                     (iListWRONG' (iRandomR (0, 3)) iExampleInt)
                     (\xs -> xs == sort xs)

coupleOrdered :: Ord a => Couple a -> Bool
coupleOrdered (One _)   = True
coupleOrdered (Two a b) = a <= b

-- | A couple of elements is always ordered
iExampleOrdered, iExampleOrdered' :: IO ()
iExampleOrdered  = checkIntegrated (iGenCouple  iExampleInt) coupleOrdered
iExampleOrdered' = checkIntegrated (iGenCouple' iExampleInt) coupleOrdered
