-- Experimental Geometric Algebra
-- With simplified add and subtract
module Data.GeoAlgType where

import ZPrelude

import Data.GeoElem (Element(..), A16(..), fromA16)
import Data.GeoTables
import Data.Array as Array
-- import ArrayIx
-- import ArrayIx as ArrayIx
import Control.Monad.ST as ST
import Data.Array.ST as STA
import Data.Enum
import Data.FunctorWithIndex
import Data.Generic.Rep (class Generic)
import Data.FoldableWithIndex
import Data.Maybe
import Data.Traversable
import Data.TraversableWithIndex
import Data.Tuple
import Safe.Coerce
import Test.QuickCheck.Arbitrary
  (class Arbitrary, arbitrary, genericArbitrary)

import Partial.Unsafe (unsafePartial)

newtype GeoAlg a = GeoAlg (Array a)

-- derive instance genericGeoAlg :: Generic (GeoAlg a) _

-- -- Used for testing.
-- instance arbitraryGeoAlg ::
--         (Generic (GeoAlg a) rep, Arbitrary rep) =>
--         Arbitrary (GeoAlg a) where
--     arbitrary = genericArbitrary

instance arbGeoAlg :: (Arbitrary a) => Arbitrary (GeoAlg a) where
  arbitrary = map ixTbl (A16
    <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
  )

instance showGeoAlg :: Show a => Show (GeoAlg a) where
  show (GeoAlg xs) = "(GeoAlg " <> show xs <> ")"

derive instance eqGeoAlg :: Eq a => Eq (GeoAlg a)

-- derive instance ordArrayIx :: Ord a => Ord (GeoAlg a)

instance foldableGeoAlg :: Foldable GeoAlg where
  foldr f x (GeoAlg xs) = foldr f x xs
  foldl f x (GeoAlg xs) = foldl f x xs
  foldMap f (GeoAlg xs) = foldMap f xs

-- Not in Test.Quickcheck.Laws
instance foldableWithIndexGeoAlg ::
  FoldableWithIndex Element GeoAlg where
    foldrWithIndex f z = foldr (\(Tuple i x) y -> f i x y) z
      <<< toArray <<< mapWithIndex Tuple
    foldlWithIndex f z = foldl (\y (Tuple i x) -> f i y x) z
      <<< toArray <<< mapWithIndex Tuple
    foldMapWithIndex = foldMapWithIndexDefaultR

-- Not in Test.Quickcheck.Laws
instance traversableGeoAlg :: Traversable GeoAlg where
    traverse f (GeoAlg xs) = GeoAlg <$> traverse f xs
    sequence (GeoAlg xs) = GeoAlg <$> sequence xs

-- Not in Test.Quickcheck.Laws
instance traversableWithIndexArrayIx ::
  TraversableWithIndex Element GeoAlg where
  traverseWithIndex = traverseWithIndexDefault

instance functorGeoAlg :: Functor GeoAlg where
  map f (GeoAlg xs) = coerce <| map f xs

instance functorWithIndexGeoAlg ::
  FunctorWithIndex Element GeoAlg where
    mapWithIndex f (GeoAlg xs) = GeoAlg <|
      Array.zipWith f (coerce bottomToTop) xs

-- | A zippy `apply`. Since `ArrayIx i a` has a length fixed
-- | by the `BoundedEnum i` an `apply` producing a product
-- | is not possible.
instance applyGeoAlg :: Apply GeoAlg where
  apply (GeoAlg fs) (GeoAlg xs) = coerce (Array.zipWith ($) fs xs)

-- | Unlike `ZipArray` we can have a `pure` since we know all
-- | compatible `ArrayIx`s have the same size.
instance applicativeGeoAlg :: Applicative GeoAlg where
  pure x = repeat x

instance semiringGeoAlg :: Ring a => Semiring (GeoAlg a) where
  add (GeoAlg xs) (GeoAlg ys) = GeoAlg <| Array.zipWith add xs ys
  zero = repeat zero
  mul = antiMult
  one = updateAt E1234 one (repeat zero)

instance ringGeoAlg :: Ring a => Ring (GeoAlg a) where
  sub (GeoAlg xs) (GeoAlg ys) = GeoAlg <| Array.zipWith sub xs ys

antiMult :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
antiMult = gMultiply gapTblIx interpGeo

infixl 7 antiMult as \./
--                    |
--                   / \

gapTblIx = ixixTbl gapTbl :: GeoAlg (GeoAlg TblEntry)

ixixTbl ::
  A16 (A16 TblEntry) -> GeoAlg (GeoAlg TblEntry)
ixixTbl xss = unsafePartial <| fromJust <| mkGeoAlgGeoAlg <|
  fromA16 <$> fromA16 xss

ixTbl :: forall a. A16 a -> GeoAlg a
ixTbl xs = unsafePartial <| fromJust <| mkGeoAlg (fromA16 xs)

gMultiply :: forall a. Ring a
  => GeoAlg (GeoAlg TblEntry)
  -> (TblEntry -> a -> a -> Tuple Element (a -> a))
  -> GeoAlg a
  -> GeoAlg a
  -> GeoAlg a
--  -> GeoAlg a
gMultiply tbl interp a b =
  unsafePartial <| fromJust <| mkGeoAlg <|
    ST.run (flip STA.withArray (toArray zero) (\res ->
      forWithIndex_ a (\i ai ->
        let
          tbli = tbl !! i
        in
          forWithIndex_ b (\j bj ->
            let
              (Tuple ix f) = interp (tbli !! j) ai bj
            in STA.modify (fromEnum ix) f res
          )
      )
    ))

interpExt :: forall a. Ring a =>
  TblEntry -> a -> a -> Tuple Element (a -> a)
interpExt entry ai bj =
  case entry of
  XP e -> Tuple e (add (ai * bj))
  XN e -> Tuple e (minus (ai * bj))
  _ -> Tuple E id

interpGeo :: forall a. Ring a =>
  TblEntry -> a -> a -> Tuple Element (a -> a)
interpGeo entry ai bj =
  case entry of
  Z -> Tuple E id
  P e -> Tuple e (add (ai * bj))
  N e -> Tuple e (minus (ai * bj))
  XP e -> Tuple e (add (ai * bj))
  XN e -> Tuple e (minus (ai * bj))
 

gUniOp :: forall a. Ring a
  => GeoAlg TblEntry
  -> GeoAlg a
  -> GeoAlg a
gUniOp tbl xs =
  unsafePartial <| fromJust <| mkGeoAlg <|
    ST.run (flip STA.withArray (toArray zero) (\res ->
        forWithIndex_ xs (\i  x ->
          let
            (Tuple ix f) = case tbl !! i of
              P e -> Tuple e (add x)
              N e -> Tuple e (minus x)
              _ -> Tuple E id
          in STA.modify (fromEnum ix) f res
        )
    ))

-- Functions that replicate `ArrayIx` functionality

toArray :: forall a. GeoAlg a -> Array a
toArray (GeoAlg xs) = xs

zipWithGeo :: forall a b c.
    (a -> b -> c) -> GeoAlg a -> GeoAlg b -> GeoAlg c
zipWithGeo f (GeoAlg xs) (GeoAlg ys) = GeoAlg <| Array.zipWith f xs ys

index :: forall a. GeoAlg a -> Element -> a
index (GeoAlg xs) e =
  unsafePartial <| Array.unsafeIndex xs <| fromEnum e

infixl 8 index as !!

updateAt :: forall a. Element -> a -> GeoAlg a -> GeoAlg a
updateAt ix x (GeoAlg xs) = GeoAlg <| unsafePartial <|
  fromJust <| Array.updateAt (fromEnum ix) x xs


mkGeoAlg :: forall a. Array a -> Maybe (GeoAlg a)
mkGeoAlg xs =
  if Array.length xs == coerce (cardinality :: Cardinality Element)
  then Just (GeoAlg xs)
  else Nothing

mkGeoAlgGeoAlg :: forall a. Array (Array a) -> Maybe (GeoAlg (GeoAlg a))
mkGeoAlgGeoAlg xs = sequence (map mkGeoAlg xs) >>= mkGeoAlg

repeat :: forall a. a -> GeoAlg a
repeat x = GeoAlg <|
  Array.replicate (coerce (cardinality :: Cardinality Element)) x

bottomToTop :: GeoAlg Element
bottomToTop = GeoAlg (enumFromTo bottom top)

