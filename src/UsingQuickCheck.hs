module UsingQuickCheck where

import           Test.QuickCheck

newtype MyInt = MyInt Int
  deriving (Show, Eq, Ord)

data MyPair a b = MyPair a b
  deriving (Show, Eq, Ord)

instance Arbitrary MyInt where
  arbitrary = MyInt <$> choose (0, 10)
  shrink (MyInt a) = [MyInt a' | a' <- [0 .. pred a]]

instance (Arbitrary a, Arbitrary b) => Arbitrary (MyPair a b) where
  arbitrary = MyPair <$> arbitrary <*> arbitrary
  shrink (MyPair a b) = concat [
                            [ MyPair a' b  | a' <- shrink a ]
                          , [ MyPair a  b' | b' <- shrink b ]
                          , [ MyPair a' b' | a' <- shrink a
                                           , b' <- shrink b ]
                          ]

example1 :: MyPair MyInt MyInt -> Bool
example1 (MyPair x y) = x < y

example2 :: MyPair MyInt MyInt -> Bool
example2 (MyPair x y) = x > y

example3 :: MyPair MyInt MyInt -> Bool
example3 (MyPair x y) = x /= y

runTest :: (Arbitrary a, Show a) => (a -> Bool) -> IO ()
runTest = quickCheck

{-------------------------------------------------------------------------------
  Simple example for blog post intro
-------------------------------------------------------------------------------}

add :: Int -> Int -> Int
add x y = x + y

newtype EvenInt = EvenInt Int
  deriving Show

instance Arbitrary EvenInt where
  arbitrary = EvenInt . (* 2) <$> arbitrary
  shrink (EvenInt n) = EvenInt <$> filter even (shrink n)

genSmallerThan :: Int -> Gen Int
genSmallerThan x = (\d -> x - 1 - abs d) <$> arbitrary

newtype Decreasing = Decreasing (Int, Int)
  deriving (Show)

instance Arbitrary Decreasing where
  arbitrary = do
      x <- arbitrary
      y <- genSmallerThan x
      return $ Decreasing (x, y)

  shrink (Decreasing (x, y)) =
      Decreasing <$> filter (uncurry (>)) (shrink (x, y))

{-------------------------------------------------------------------------------
  Wrapper around Int that picks uniformly (unaffected by size)
-------------------------------------------------------------------------------}

newtype Uniform = Uniform Int
  deriving (Show)

instance Arbitrary Uniform where
  arbitrary = Uniform <$> choose (0, 100)
  shrink (Uniform n) = Uniform <$> shrink n
