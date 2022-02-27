module Data.GeoAlgParts where

import ZPrelude

import Data.GeoAlgType
import Data.GeoElem
import Data.Foldable
import Data.Generic.Rep (class Generic)
import Data.HeytingAlgebra (implies, tt, ff)
import Test.QuickCheck.Arbitrary
  (class Arbitrary, arbitrary, genericArbitrary)


data GeoPart a = Zed
    | Mag a a
    | Point a a a a
    | Line a a a a a a
    | Plane a a a a
    | Motor a a a a a a a a
    | Flector a a a a a a a a
    | GeoAll a a a a a a a a a a a a a a a a


derive instance genericGeoPart :: Generic (GeoPart a) _

-- Used for testing.
instance arbitraryGeoPart ::
        (Generic (GeoPart a) rep, Arbitrary rep) =>
        Arbitrary (GeoPart a) where
    arbitrary = genericArbitrary

derive instance eqGeoPart :: Eq a => Eq (GeoPart a)

z0 = zero :: forall a. Semiring a => a

toGeoAlg :: forall a. Ring a => GeoPart a -> GeoAlg a
toGeoAlg = case _ of
  Zed -> zero
  Mag x y -> ixTbl <|
    A16 x   z0 z0 z0 z0  z0 z0 z0 z0 z0 z0  z0 z0 z0 z0  y
  Point px py pz pw -> ixTbl <|
    A16 z0  px py pz pw  z0 z0 z0 z0 z0 z0  z0 z0 z0 z0  z0
  Line mx my mz vx vy vz -> ixTbl <|
    A16 z0  z0 z0 z0 z0  mx my mz vx vy vz  z0 z0 z0 z0  z0
  Plane fx fy fz fw -> ixTbl <|
    A16 z0  z0 z0 z0 z0  z0 z0 z0 z0 z0 z0  fx fy fz fw  z0
  Motor uw ux uy uz rx ry rz rw -> ixTbl <|
    A16 uw  z0 z0 z0 z0  ux uy uz rx ry rz  z0 z0 z0 z0  rw
  Flector sx sy sz sw hx hy hz hw -> ixTbl <|
    A16 z0  sx sy sz sw  z0 z0 z0 z0 z0 z0  hx hy hz hw  z0
  GeoAll x px py pz pw mx my mz vx vy vz fx fy fz fw y -> ixTbl <|
    A16 x  px py pz pw  mx my mz vx vy vz  fx fy fz fw  y

subset :: forall a. Semiring a => Eq a =>
  GeoAlg Boolean -> GeoAlg a -> Boolean
subset aVec = and << zipWithGeo implies aVec << map (eq zero)

-- Bulk and weight? Representation?
fromGeoAlg :: forall a. Eq a => Semiring a => GeoAlg a -> GeoPart a
fromGeoAlg geo = case toArray geo of
  [e, e1, e2, e3, e4, e23, e31, e12, e43, e42, e41, e321, e124, e314, e234, e1234]
    | all (eq zero) geo -> Zed
    | subset magVec geo -> Mag e e1234
    | subset pointVec geo -> Point e1 e2 e3 e4
    | subset lineVec geo -> Line e23 e31 e12 e43 e42 e41
    | subset planeVec geo -> Plane e321 e124 e314 e234
    | subset motorVec geo -> Motor e e23 e31 e12 e43 e42 e41 e1234
    | subset flectorVec geo -> Flector e1 e2 e3 e4 e321 e124 e314 e234
    | otherwise ->
      GeoAll e e1 e2 e3 e4 e23 e31 e12 e43 e42 e41 e321 e124 e314 e234 e1234
  _ -> Zed

-- fromGeoAlg1 :: forall a. Eq a => Semiring a => GeoAlg a -> GeoPart a
-- fromGeoAlg1 geo = case toArray geo of
--   [z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0] ->
--     Zed
--   [x, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, z0, y] ->
--     Mag x y
--   [e, e1, e2, e3, e4, e23, e31, e12, e43, e42, e41, e321, e124, e314, e234, e1234] ->
--     GeoAll e e1 e2 e3 e4 e23 e31 e12 e43 e42 e41 e321 e124 e314 e234 e1234


magVec :: forall a. HeytingAlgebra a => GeoAlg a
magVec = ixTbl <|
  A16 ff tt tt tt tt tt tt tt tt tt tt tt tt tt tt ff

pointVec :: forall a. HeytingAlgebra a => GeoAlg a
pointVec = ixTbl <|
  A16 tt ff ff ff ff tt tt tt tt tt tt tt tt tt tt tt

lineVec :: forall a. HeytingAlgebra a => GeoAlg a
lineVec = ixTbl <|
  A16 tt tt tt tt tt ff ff ff ff ff ff tt tt tt tt tt

planeVec :: forall a. HeytingAlgebra a => GeoAlg a
planeVec = ixTbl <|
  A16 tt tt tt tt tt tt tt tt tt tt tt ff ff ff ff tt

motorVec :: forall a. HeytingAlgebra a => GeoAlg a
motorVec = ixTbl <|
  A16 ff tt tt tt tt ff ff ff ff ff ff tt tt tt tt ff

flectorVec :: forall a. HeytingAlgebra a => GeoAlg a
flectorVec = ixTbl <|
  A16 tt ff ff ff ff tt tt tt tt tt tt ff ff ff ff tt

magElem :: GeoPart Element
magElem = Mag E E1234

pointElem :: GeoPart Element
pointElem = Point E1 E2 E3 E4

lineElem :: GeoPart Element
lineElem = Line E23 E31 E12 E43 E42 E41

planeElem :: GeoPart Element
planeElem = Plane E321 E124 E314 E234

motorElem :: GeoPart Element
motorElem = Motor E E23 E31 E12 E43 E42 E41 E1234

flectorElem :: GeoPart Element
flectorElem = Flector E1 E2 E3 E4 E321 E124 E314 E234

geoAllElem :: GeoPart Element
geoAllElem =
  GeoAll E E1 E2 E3 E4 E23 E31 E12 E43 E42 E41 E321 E124 E314 E234 E1234


-- data GeoPart a = Zeros
--   | Mag (Array a)
--   | Point Array a
--   | Line Array a
--   | Plane Array a
--   | Motor Array a
--   | Flector Array a
  

-- Reduction / Extraction
-- Is it all zero?
-- Is it bulk or weight?
-- Is it a magnitude?
-- Is it a point?
-- Is it a line?
-- Is it a plane?
-- Is it a motor?
-- Is it a flector?


-- Mag(2)       Scalar(1)         Antiscalar(1)
-- Point(4)     Point bulk(3)     Point wght(1)
-- Line(6)      Line bulk(3)      Line wght(3)
-- Plane(4)     Plane bulk(1)     Plane wght(3)
-- Motor(8)     Motor bulk(4)     Motor wght(4)       Mag + Line
-- Flector(8)   Flector bulk(4)   Flector wght(4)     Point + Plane
-- GeoAlg(16)   GeoAlg bulk(8)    GeoAlg wght(8)      Motor + Flector

-- type Mag a = {e::a, e1234::a}

-- instance name :: X GeoAlg
-- else instance name :: X Flector
-- else instance name :: X Motor
-- else instance name :: X Line
-- else instance name :: X Plane
-- else instance name :: X Point
-- else instance name :: X Line wght
-- else instance name :: X Line bulk
-- else instance name :: X Plane wght
-- else instance name :: X Point bulk
-- else instance name :: X Mag
-- else instance name :: X Scalar
-- else instance name :: X Pseudo

-- Need `Element` vector for GeoAlg
-- Need index vector for each type (use size vectors?)
-- Data itself kept in Arrays (use size vectors?)
-- Reduce / Optimize calculate operation




