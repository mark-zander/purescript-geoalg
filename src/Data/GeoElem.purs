module Data.GeoElem
  ( A16(..)
  , Element(..)
  , fromA16
  , toA16
  )
  where

import ZPrelude

import Data.Enum (class BoundedEnum, class Enum)
import Data.Generic.Rep (class Generic)
import Data.Bounded.Generic (genericBottom, genericTop)
import Data.Enum.Generic (genericCardinality,
    genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Test.QuickCheck.Arbitrary
  (class Arbitrary, class Coarbitrary, genericArbitrary, genericCoarbitrary)

-- | `Element`s of Geometric Algebra
data Element = E | E1 | E2 | E3 | E4 |
    E23 | E31 | E12 | E43 | E42 | E41 |
    E321 | E124 | E314 | E234 | E1234

-- | Data structure that has exactly 16 values
-- | which matches the number of `Element`s.
data A16 a = A16 a a a a a a a a a a a a a a a a

toA16 :: forall a. Array a -> Maybe (A16 a)
toA16 [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]
    = Just (A16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
toA16 _ = Nothing

fromA16 :: forall a. A16 a -> Array a
fromA16 (A16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) =
  [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]

-- Used for testing.
instance arbitraryElement ::
        (Generic Element rep, Arbitrary rep) =>
        Arbitrary Element where
    arbitrary = genericArbitrary

-- Used for testing.
instance coarbitraryElement ::
        (Generic Element rep, Coarbitrary rep) =>
        Coarbitrary Element where
    coarbitrary = genericCoarbitrary

derive instance eqElement :: Eq Element
derive instance ordElement :: Ord Element
derive instance genericElement :: Generic Element _
instance showElement :: Show Element where
  show = genericShow
instance boundedElement :: Bounded Element where
  bottom = genericBottom   
  top = genericTop
instance enumElement :: Enum Element where
  succ = genericSucc
  pred = genericPred
instance boundedenumElement :: BoundedEnum Element where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum
