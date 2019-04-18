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

data SomeRecord = SomeRecord {
      someInt    :: Int
    , someDouble :: Double
    } deriving (Eq, Show)

genRecord :: Gen SomeRecord
genRecord = SomeRecord
    <$> Gen.int    (Range.constant 0 1000)
    <*> Gen.double (Range.constant 0 20)

-- Often not minimal
prop_record :: Property
prop_record = property $ do
    x <- forAll genRecord
    assert $ fromIntegral (someInt x) < (someDouble x)
