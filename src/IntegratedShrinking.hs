{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module IntegratedShrinking where

import           Control.Monad hiding (join)
import           Data.List     (intercalate, sort)
import           Data.Maybe    (fromJust, listToMaybe, mapMaybe)
import           GHC.Stack
import qualified System.Random as R

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

pickOne :: [a] -> [([a], a, [a])]
pickOne []     = []
pickOne [x]    = [([], x, [])]
pickOne (x:xs) = ([], x, xs)
               : map (\(as, b, cs) -> (x:as, b, cs)) (pickOne xs)

repeatUntil :: forall m a. Monad m => (a -> Bool) -> m a -> m a
repeatUntil p ma = search
  where
    search :: m a
    search = ma >>= \a -> if p a then return a else search

data Marked a = Marked { marked :: a , isFirst :: Bool , isLast :: Bool }
  deriving (Show)

mark :: [a] -> [Marked a]
mark = \case
    []     -> []
    [x]    -> [Marked x True True]
    (x:xs) -> Marked x True False : go xs
  where
    go :: [a] -> [Marked a]
    go []     = error "mark: empty list"
    go [x]    = [Marked x False True]
    go (x:xs) = Marked x False False : go xs

replicateA :: Applicative f => Word -> f a -> f [a]
replicateA 0 _ = pure []
replicateA n f = (:) <$> f <*> replicateA (n - 1) f

{-------------------------------------------------------------------------------
  Manual shrinking

  We do not use a StateT-like style because we want to be able to generate
  infinite structures.
-------------------------------------------------------------------------------}

newtype Gen a = Gen (R.StdGen -> a)
  deriving (Functor)

runGen :: R.StdGen -> Gen a -> a
runGen prng (Gen g) = g prng

instance Applicative Gen where
  pure  = return
  (<*>) = ap

instance Monad Gen where
  return x = Gen $ \_prng -> x
  x >>= f  = Gen $ \ prng ->
    let (prngX, prngF) = R.split prng
    in runGen prngF (f (runGen prngX x))

data Manual a = Manual {
      gen    :: Gen a
    , shrink :: a -> [a]
    }

{-------------------------------------------------------------------------------
  Examples of 'Manual' instances
-------------------------------------------------------------------------------}

-- | Generate random 'Bool', shrinking 'True' to 'False'
mBool :: Manual Bool
mBool = Manual {
      gen    = Gen (fst . R.random)
    , shrink = \b -> case b of
                       True  -> [False]
                       False -> []
    }

-- | Generate random value in the closed interval from @0@ to @hi@.
--
-- Shrinks using binary search to lower bound.
mWord :: Word -> Manual Word
mWord hi = Manual {
      gen    = Gen (fst . R.randomR (0, hi))
    , shrink = \x -> concat [
                         [ x `div` 2 | x > 2 ]
                       , [ x - 1     | x > 0 ]
                       ]
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
                   [ (x', y) | x' <- shrink genA x ]
                   -- Shrink the right element
                 , [ (x, y') | y' <- shrink genB y ]
                 ]
    }

mList :: Manual Word -> Manual a -> Manual [a]
mList genLen genA = Manual {
      gen    = do n <- gen genLen
                  replicateM (fromIntegral n) (gen genA)
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
      gen    = repeatUntil p $ gen genA
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
      gen    = repeatUntil p $ gen genA
    , shrink = filter p . shrink genA
    }

-- | Generate even number in range from @0@ to @hi@.
--
-- We use 'mSuchThat' rather than 'mSuchThat_' because the latter would result
-- in poor shrinks:
--
-- > shrink (mWord 10                  ) 10 == [5, 9]
-- > shrink (mWord 10 `mSuchThat`  even) 10 == [2,4,4,8]
-- > shrink (mWord 10 `mSuchThat_` even) 10 == []
mEven :: Word -> Manual Word
mEven hi = mWord hi `mSuchThat` even

-- | Wrong version of 'mEven'
mEvenWRONG :: Word -> Manual Word
mEvenWRONG hi = mWord hi `mSuchThat_` even

-- | Alternative definition of 'mEven'
--
-- Generate-then-test is always slower than generators of values that we /know/
-- must satisfy the predicate (this may or may not matter, depending on the
-- probability that a randomly generated value satisfies the predicate).
--
-- However, note that the logic for " evenness " now lives in both the generator
-- and in the shrinker, and we cannot really re-use any existing code.
-- Integrated shrinking has a better story here.
mEven' :: Word -> Manual Word
mEven' hi = Manual {
      gen    = (*2) <$> gen (mWord (hi `div` 2))
    , shrink = \x -> concat [
                         [ x `div` 2     | even (x `div` 2) ]
                       , [ x `div` 2 - 1 | odd  (x `div` 2) ]
                       , [ x - 2         | x > 1            ]
                       ]
    }

{-------------------------------------------------------------------------------
  Trees
-------------------------------------------------------------------------------}

data Tree a = Node { root :: a , subtrees :: [Tree a] }
  deriving (Functor, Show)

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
join (Node (Node x xs) xss) = Node x (map join xss ++ xs)

{-------------------------------------------------------------------------------
  Also as for 'Applicative', however, we can change the ordering of the
  subtrees whilst still preserving the same properties.

  (This also means 'Tree' has (at least) /four/ 'Applicative' instances.)

  However, 'join'' is strictly worse: 'join' already introduces a strict
  ordering between left and right, never going back to left if it can shrink
  right; 'join'' tries to shrink the right /first/.
-------------------------------------------------------------------------------}

join' :: Tree (Tree a) -> Tree a
join' (Node (Node x xs) xss) = Node x (xs ++ map join' xss)

{-------------------------------------------------------------------------------
  To aid debugging: tree rendering
-------------------------------------------------------------------------------}

renderTree :: Tree String -> String
renderTree = intercalate "\n" . go
  where
    go :: Tree String -> [String]
    go (Node x xs) = x : concatMap inset (mark (map go xs))

    inset :: Marked [String] -> [String]
    inset Marked{..} =
        case (isLast, marked) of
          (_,     []  ) -> error "inset: empty list"
          (True,  s:ss) -> ("└─ " ++ s) : map ("   " ++) ss
          (False, s:ss) -> ("├─ " ++ s) : map ("│  " ++) ss

{-------------------------------------------------------------------------------
  Integrated shrinking
-------------------------------------------------------------------------------}

newtype Integrated a = Integrated (R.StdGen -> Tree a)
  deriving (Functor)

runIntegrated :: R.StdGen -> Integrated a -> Tree a
runIntegrated prng (Integrated f) = f prng

instance Applicative Integrated where
  pure x = Integrated $ \_prng -> singleton x
  Integrated f <*> Integrated x = Integrated $ \prng ->
    let (prngF, prngX) = R.split prng
    in interleave (f prngF) (x prngX)

newtype Dependent a = Dependent (R.StdGen -> Tree a)
  deriving (Functor)

runDependent :: R.StdGen -> Dependent a -> Tree a
runDependent prng (Dependent f) = f prng

lift :: Integrated a -> Dependent a
lift (Integrated f) = Dependent f

unsafeIndependent :: Dependent a -> Integrated a
unsafeIndependent (Dependent f) = Integrated f

instance Applicative Dependent where
  pure  = return
  (<*>) = ap

instance Monad Dependent where
  return x = Dependent $ \_prng -> singleton x
  Dependent x >>= f = Dependent $ \prng ->
    let (prngX, prngF) = R.split prng
    in join $ fmap (runDependent prngF . f) (x prngX)

{-------------------------------------------------------------------------------
  From 'Manual' to 'Integrated'
-------------------------------------------------------------------------------}

integrated :: Manual a -> Integrated a
integrated Manual{..} = Integrated $ \prng ->
    unfoldTree shrink $ runGen prng gen

{-------------------------------------------------------------------------------
  This is useful to define "primitive" integrated shrinkers
-------------------------------------------------------------------------------}

iBool :: Integrated Bool
iBool = integrated $ mBool

iWord :: Word -> Integrated Word
iWord = integrated . mWord

{-------------------------------------------------------------------------------
  As long as we just need 'Applicative', defining composite integrated
  shrinkers is easy. Indeed, we don't really need to provide such combinators
  at all.
-------------------------------------------------------------------------------}

iPair :: Integrated a -> Integrated b -> Integrated (a, b)
iPair genA genB = (,) <$> genA <*> genB

iTriple :: Integrated a -> Integrated b -> Integrated c -> Integrated (a, b, c)
iTriple genA genB genC = (,,) <$> genA <*> genB <*> genC

-- | Generate list of fixed size
iListOfSize :: Word -> Integrated a -> Integrated [a]
iListOfSize = replicateA

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
iPairWRONG genA genB = unsafeIndependent $ ((,) <$> lift genA) `ap` lift genB

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
iListWRONG :: Integrated Word -> Integrated a -> Integrated [a]
iListWRONG genLen genA = unsafeIndependent $ do
    n <- lift genLen
    replicateM (fromIntegral n) (lift genA)

-- | Another invalid generator for lists
--
-- Although this one is slightly better as the elements as now independent
-- from each other, we still introduce an unnecessary ordering between picking
-- the length of the list and the elements.
--
-- As before, the absence of the 'Monad' instance helps avoid this definition.
iListWRONG' :: Integrated Word -> Integrated a -> Integrated [a]
iListWRONG' genLen genA = unsafeIndependent $ do
    n <- lift genLen
    lift $ iListOfSize n genA

-- | Make the shrink tree explicitly available
--
-- This is very useful when we need to override shrinking.
--
-- See 'iList' for an example.
freeze :: Integrated a -> Dependent (Tree a)
freeze (Integrated f) = Dependent $ singleton . f

-- | Just keep the root of the shrink tree
dontShrink :: Integrated a -> Dependent a
dontShrink (Integrated f) = Dependent $ singleton . root . f

-- | Turn generator with explicit shrinking back into an integrated shrinker
dependent  :: HasCallStack => Dependent (Tree a) -> Integrated a
dependent (Dependent f) = Integrated $ \prng ->
    case f prng of
      Node a []  -> a
      _otherwise -> error "dependent: unexpected subtrees"

-- | Auxiliary to 'iList'
iListAux :: Integrated Word -> Integrated a -> Dependent [Tree a]
iListAux genLen genA = do
    n <- dontShrink genLen
    replicateM (fromIntegral n) (freeze genA)

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

-- | Generate list of elements
--
-- Note the use of 'dontShrink': this establishes the invariant that
-- 'dependent' relies on.
iList :: Integrated Word -> Integrated a -> Integrated [a]
iList genLen genA = dependent $ (interleaveList <$> iListAux genLen genA)

{-------------------------------------------------------------------------------
  Example: counting
-------------------------------------------------------------------------------}

data Count a = Zero | One a | Two a a
  deriving (Show)

couple :: [a] -> Count a
couple []         = Zero
couple [a]        = One a
couple [a, b]     = Two a b
couple _otherwise = error "couple: too many elements"

-- | Auxiliary to 'iGenCouple'
iGenCoupleAux :: Integrated a -> Dependent (Count (Tree a))
iGenCoupleAux genA = do
    n <- dontShrink (iWord 2)
    couple <$> replicateM (fromIntegral n) (freeze genA)

interleaveCount :: Count (Tree a) -> Tree (Count a)
interleaveCount Zero =
    Node Zero []
interleaveCount (One a)   =
    Node (One (root a)) $ concat [
        -- Drop the element
        [ interleaveCount Zero ]
        -- Shrink an element
      , [ interleaveCount (One a') | a' <- subtrees a ]
      ]
interleaveCount (Two a b) =
    Node (Two (root a) (root b)) $ concat [
        -- Drop an element
        [ interleaveCount (One a) ]
      , [ interleaveCount (One b) ]
        -- Shrink an element
      , [ interleaveCount (Two a' b ) | a' <- subtrees a ]
      , [ interleaveCount (Two a  b') | b' <- subtrees b ]
      ]

-- | Generator for 'Count' in the same style as we did for lists
--
-- This demonstrates that the pattern scales to other datatypes.
iGenCouple :: forall a. Integrated a -> Integrated (Count a)
iGenCouple genA = dependent $ interleaveCount <$> iGenCoupleAux genA

-- | Variation on 'iGenCouple'
--
-- Here we can really benefit from integrated shrinking: we just reuse the
-- one for lists: the 'Count' will shrink as the list does.
iGenCouple' :: Integrated a -> Integrated (Count a)
iGenCouple' = fmap couple . iList (iWord 2)

-- | Pair a 'Count' with the list that generated it
data WrappedCouple a = WrappedCouple [a] (Count a)

wrappedCouple :: [a] -> WrappedCouple a
wrappedCouple xs = WrappedCouple xs (couple xs)

-- | Attempt to define the equivalent of 'iGenCouple'' using manual shrinking
--
-- Note that this requires a wrapper type, and hence we lose compositionaly
-- (if we have other types that need 'Count's as subterms, we cannot use
-- 'WrappedCouple'). An real-life example of this is QuickCheck's
-- 'Function' type.
mGenCouple' :: forall a. Manual a -> Manual (WrappedCouple a)
mGenCouple' genA = Manual {
      gen    = wrappedCouple <$> gen genAs
    , shrink = \(WrappedCouple xs _) -> map wrappedCouple (shrink genAs xs)
    }
  where
    genAs :: Manual [a]
    genAs = mList (mWord 2) genA

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
iSuchThatWRONG genA p = unsafeIndependent $ repeatUntil p $ lift genA

-- | Filter out elements that do not satisfy the predicate
iSuchThat :: forall a. Integrated a -> (a -> Bool) -> Integrated a
iSuchThat genA p =
    dependent $ fmap filterTree' $
      repeatUntil (p . root) $ freeze genA
  where
    -- We know that the top-level element /must/ satisfy the predicate
    filterTree' :: Tree a -> Tree a
    filterTree' t = case filterTree p t of
                      [t']       -> t'
                      _otherwise -> error "filterTree: impossible"

-- | Faster version of 'iSuchThat'
--
-- This is a version of 'iSuchThat' that does not attempt to shrink a value that
-- does not satisfy the predicate any further. It trades shrinking performance
-- for the quality of the shrinks.
iSuchThat_ :: forall a. Integrated a -> (a -> Bool) -> Integrated a
iSuchThat_ genA p =
    dependent $ fmap filterTree' $
      repeatUntil (p . root) $ freeze genA
  where
    -- We know that the top-level element /must/ satisfy the predicate
    filterTree' :: Tree a -> Tree a
    filterTree' = fromJust . filterTree_ p

{-------------------------------------------------------------------------------
  Example: even numbers
-------------------------------------------------------------------------------}

-- | Produce an even number in range from @0@ to @hi@.
--
-- Note that the use of 'iSuchThat_' here would produce poor shrinks.
iEven :: Word -> Integrated Word
iEven hi = iWord hi `iSuchThat` even

-- | Variation on 'iEven' using the wrong filter
iEvenWRONG :: Word -> Integrated Word
iEvenWRONG hi = iWord hi `iSuchThat_` even

-- | Alternative definition of 'iEven'
--
-- This is a nice example where we can really benefit from integrated shrinking.
iEven' :: Word -> Integrated Word
iEven' hi = (*2) <$> iWord (hi `div` 2)

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
    case findCounterexample p (root (runIntegrated (R.mkStdGen seed) genAs)) of
      Nothing ->
        putStrLn $ "OK"
      Just shrinkSteps -> do
        putStrLn $ "Failed: " ++ show (head shrinkSteps)
        putStrLn $ "Shrinking: " ++ show shrinkSteps
        putStrLn $ "Shrunk: " ++ show (last shrinkSteps)
  where
    numTests :: Int
    numTests = 100

    genAs :: Integrated [Tree a]
    genAs = unsafeIndependent $ replicateM numTests (freeze genA)

-- | Find counter example to the specified property
--
-- If a counter-example was found, returns all shrink steps taken
-- (first element of the list is the original counter example, last the
-- minimal test case).
--
-- NOTE: This hardcodes another point where we stop early, rather than
-- continue shrinking.
findCounterexample :: forall a. (a -> Bool) -> [Tree a] -> Maybe [a]
findCounterexample p =
      fmap minimize
    . listToMaybe
    . filter (not . p . root)
  where
    minimize :: Tree a -> [a]
    minimize (Node x xs) =
        case filter (not . p . root) xs of
          []   -> [x]
          x':_ -> x : minimize x'

checkManual :: Show a => Manual a -> (a -> Bool) -> IO ()
checkManual = checkIntegrated . integrated

checkManualWith :: forall a. Show a
                => Seed -> Manual a -> (a -> Bool) -> IO ()
checkManualWith seed = checkIntegratedWith seed . integrated

{-------------------------------------------------------------------------------
  Example top-level calls
-------------------------------------------------------------------------------}

mExampleWord :: Manual Word
mExampleWord = mWord 100

iExampleWord :: Integrated Word
iExampleWord = iWord 100

-- | All numbers are less than 12.
mExampleTwelve :: IO ()
mExampleTwelve = checkManual mExampleWord (< 12)

-- | All numbers are even
--
-- This shows that we /still/ may not shrink all the way, because
-- 'findCounterexample' stops as soon as shrinking yields only values that
-- are not counter-examples anymore.
mExampleEven :: IO ()
mExampleEven = checkManual mExampleWord even

-- | All even numbers are less than 5
--
-- Note how 'mExampleEven5''' does not shrink properly.
mExampleEven5, mExampleEven5', mExampleEven5'' :: IO ()
mExampleEven5   = checkManual (mEven      100) (< 5)
mExampleEven5'  = checkManual (mEven'     100) (< 5)
mExampleEven5'' = checkManual (mEvenWRONG 100) (< 5)

-- | All even numbers are less than 5
--
-- As above, 'iExampleEven5''' shrinks poorly.
iExampleEven5, iExampleEven5', iExampleEven5'' :: IO ()
iExampleEven5   = checkIntegrated (iEven      100) (< 5)
iExampleEven5'  = checkIntegrated (iEven'     100) (< 5)
iExampleEven5'' = checkIntegrated (iEvenWRONG 100) (< 5)

-- | First element is always less than the second element of a pair
mExampleLess, iExampleLess, iExampleLess' :: IO ()
mExampleLess  = checkManual
                  (mPair mExampleWord mExampleWord)
                  (uncurry (<))
iExampleLess  = checkIntegrated
                  (iPair iExampleWord iExampleWord)
                  (uncurry (<))
iExampleLess' = checkIntegrated
                  (iPairWRONG iExampleWord iExampleWord)
                  (uncurry (<))

-- | All pairs contain two different values
mExampleEqual :: IO ()
mExampleEqual = checkManual
                  (mPair mExampleWord mExampleWord)
                  (uncurry (/=))

-- | All lists are sorted
mExampleSorted, iExampleSorted, iExampleSorted', iExampleSorted'' :: IO ()
mExampleSorted   = checkManual
                     (mList (mWord 3) mExampleWord)
                     (\xs -> xs == sort xs)
iExampleSorted   = checkIntegrated
                     (iList (iWord 3) iExampleWord)
                     (\xs -> xs == sort xs)
iExampleSorted'  = checkIntegrated
                     (iListWRONG (iWord 3) iExampleWord)
                     (\xs -> xs == sort xs)
iExampleSorted'' = checkIntegrated
                     (iListWRONG' (iWord 3) iExampleWord)
                     (\xs -> xs == sort xs)

coupleOrdered :: Ord a => Count a -> Bool
coupleOrdered Zero      = True
coupleOrdered (One _)   = True
coupleOrdered (Two a b) = a <= b

-- | A couple of elements is always ordered
iExampleOrdered, iExampleOrdered' :: IO ()
iExampleOrdered  = checkIntegrated (iGenCouple  iExampleWord) coupleOrdered
iExampleOrdered' = checkIntegrated (iGenCouple' iExampleWord) coupleOrdered

-- | Just to demonstrate greediness
--
-- 'iExampleGreedyM' shinks correctly when using 'join'' but not with 'join'
iExampleGreedyA, iExampleGreedyM :: IO ()
iExampleGreedyA = checkIntegrated (iPair      iExampleWord iExampleWord) (\(x, y) -> x + y == 0)
iExampleGreedyM = checkIntegrated (iPairWRONG iExampleWord iExampleWord) (\(x, y) -> x + y == 0)

mExampleSumLength, mExampleGreaterLen :: IO ()
mExampleSumLength  = checkManual
                       (mList (mWord 3) mExampleWord)
                       (\xs -> sum xs <= fromIntegral (length xs))
mExampleGreaterLen = checkManual
                       (mList (mWord 3) mExampleWord)
                       (\xs -> all (\x -> x >= fromIntegral (length xs)) xs)

{-------------------------------------------------------------------------------
  Mostly to aid writing the blog post
-------------------------------------------------------------------------------}

-- | Variation on 'checkIntegrated' that doesn't just look for /any/
-- counter-example, but one that satisfies a predicate. Useful when looking for
-- small examples.
findIntegrated :: forall a. Show a
               => Integrated a -> (a -> Bool) -> ([a] -> Bool) -> IO ()
findIntegrated genA p p' = go
  where
    go :: IO ()
    go = do
        seed <- R.randomIO
        case findCounterexample p (root (runIntegrated (R.mkStdGen seed) genAs)) of
          Just shrinkSteps | p' shrinkSteps -> do
            putStrLn $ "Using seed " ++ show seed
            putStrLn $ "Shrinking: " ++ show shrinkSteps
          _otherwise -> go

    numTests :: Int
    numTests = 100

    genAs :: Integrated [Tree a]
    genAs = unsafeIndependent $ replicateM numTests (freeze genA)

-- | Analogue of 'findIntegrated' for manual shrinkers.
findManual :: Show a => Manual a -> (a -> Bool) -> ([a] -> Bool) -> IO ()
findManual = findIntegrated . integrated

-- | Show random tree that satisfies the given property
showTree :: forall a. Show a => Integrated a -> (Tree a -> Bool) -> IO ()
showTree g p =
    find >>= putStrLn . renderTree . fmap show
  where
    find :: IO (Tree a)
    find = repeatUntil p $ (\s -> runIntegrated (R.mkStdGen s) g) <$> R.randomIO
