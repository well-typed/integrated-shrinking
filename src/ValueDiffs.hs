-- The value diffs example from
--
-- "YOW! Lambda Jam 2017 Jacob Stanley - Gens N’ Roses: Appetite for Reduction #YOWLambdaJam
-- <https://www.youtube.com/watch?v=AIv_9T0xKEo> (27:35)
--
-- Also available in hedgehog-example in the Hedgehog git repo
module ValueDiffs where

import Hedgehog
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

data SomeRecord =
  SomeRecord {
      someInt :: Int
    , someBool :: Bool
    , someDouble :: Double
    , someList :: [(Int, String)]
    } deriving (Eq, Show)

genRecord :: Gen SomeRecord
genRecord =
  SomeRecord
    <$> Gen.int (Range.linearFrom 0 (-1000) 1000)
    <*> Gen.bool
    <*> Gen.double (Range.linearFrac 7.2 15.9)
    <*> Gen.list (Range.linear 5 100)
          ((,)
            <$> Gen.int (Range.constant 0 10)
            <*> Gen.string (Range.constant 2 4) Gen.alpha)

prop_record :: Property
prop_record =
  property $ do
    x <- forAll genRecord
    y <- forAll genRecord
    x === y

-- Often not minimal
prop_harder :: Property
prop_harder =
  property $ do
    x <- forAll genRecord
    assert $ fromIntegral (someInt x) < (someDouble x)
