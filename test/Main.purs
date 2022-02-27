module Test.Main where

import ZPrelude

import Effect (Effect, forE, foreachE)
import Effect.Class.Console (log)
import Data.Array (length, (!!), (..), zipWith)
import Data.Maybe
import Data.Foldable
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)
import Test.QuickCheck
import Test.QuickCheck.Laws (checkLaws)
import Test.QuickCheck.Laws.Data as Data
import Test.QuickCheck.Laws.Control as Control
import Type.Proxy (Proxy(..), Proxy2(..))

import Data.GeoTables
import Data.GeoElem
import Data.GeoAlgType
import Data.GeoAlgFcn
import Data.GeoAlgParts

aGeoInt :: GeoAlg Int -> GeoAlg Int
aGeoInt = id

prxGeoPart = Proxy :: Proxy (GeoPart Int)
prxGeoAlg = Proxy :: Proxy (GeoAlg Int)
prx2GeoAlg = Proxy2 :: Proxy2 GeoAlg
prxElement = Proxy :: Proxy Element

main :: Effect Unit
main = do
  -- sizeTest
  -- subsetTest
  -- quickCheck \x y -> eq (aScalarInt x + y) (y + x)
  -- quickCheck \x y -> eq (aGeoInt x + y) (y + x)
  checkLaws "Element" do
    Data.checkEq prxElement
    Data.checkOrd prxElement
    Data.checkBounded prxElement
    Data.checkBoundedEnum prxElement

  checkLaws "GeoAlg" do
    Data.checkSemiring prxGeoAlg
    Data.checkRing prxGeoAlg
    Data.checkEq prxGeoAlg
    Data.checkFoldable prx2GeoAlg
    Data.checkFunctor prx2GeoAlg
    Data.checkFunctorWithIndex prx2GeoAlg
    Control.checkApply prx2GeoAlg
    Control.checkApplicative prx2GeoAlg

  checkGeoMult "Geometric Product" geoMult p1 prxGeoAlg
  checkGeoMult "Exterior Product" geoExt p1 prxGeoAlg
  checkGeoMult "Geometric Antiproduct" antiMult one prxGeoAlg
  checkGeoMult "Exterior Antiproduct" antiExt one prxGeoAlg

  checkDeMorgan "Geometric Product" geoMult antiMult prxGeoAlg
  checkDeMorgan "Exterior Product" geoExt antiExt prxGeoAlg

  checkCmpl prxGeoAlg

  log "Checking GeoPart -> GeoAlg -> GeoPart"
  quickCheck' 1000 (checkGeoPartToGeoAlg prxGeoPart) where
    checkGeoPartToGeoAlg :: forall a. Ring a => Eq a => Arbitrary a =>
      Proxy (GeoPart a) -> GeoPart a -> Boolean
    checkGeoPartToGeoAlg _ geoPart =
      fromGeoAlg (toGeoAlg geoPart) == geoPart


checkCmpl :: forall a. Ring a => Eq a => Arbitrary a =>
  Proxy (GeoAlg a) -> Effect Unit
checkCmpl _ = do
  log "Checking Bulk and Weight"
  quickCheck checkBulkWght

  log "Checking cmplL cmplR"
  quickCheck checkCmplLCmplR

  -- Works for elements not multivectors?
  -- log "Checking Interior Anti Product"
  -- quickCheck checkInteriorAntiProd

  -- log "Checking cmplement functions"
  -- quickCheck checkCmplFcns

  where

  checkBulkWght :: GeoAlg a -> Boolean
  checkBulkWght geo = bulk geo + wght geo == geo

  checkCmplLCmplR :: GeoAlg a -> Boolean
  checkCmplLCmplR geo = cmplL (cmplR geo) == geo

  -- checkInteriorAntiProd :: GeoAlg a -> GeoAlg a -> Boolean
  -- checkInteriorAntiProd  a b =
  --   a |= b == cmplR (a -| b) && a =| b == cmplL (a |- b)

  -- checkCmplFcns :: GeoAlg a -> Boolean
  -- checkCmplFcns a =
  --   cmplL a == rev a /.\ one + p1 \./ rev a &&
  --   cmplR a == arev a /.\ one + p1 \./ arev a

p1 :: forall a. Semiring a => GeoAlg a
p1 = updateAt E one (repeat zero)

checkGeoMult :: forall a. Ring a => Eq a => Arbitrary a =>
  String ->
  (GeoAlg a -> GeoAlg a -> GeoAlg a) ->
  GeoAlg a ->
  Proxy (GeoAlg a) ->
  Effect Unit
checkGeoMult msg mult unit _ = do
  log ("Checking 'Scalar Factor' law for " <> msg)
  quickCheck' 1000 scalarFactor

  log ("Checking 'Associativity' law for " <> msg)
  quickCheck' 1000 associativeGeoMult

  log ("Checking 'Identity' law for " <> msg)
  quickCheck' 1000 identityGeoMult

  log ("Checking 'Left distribution' law for " <> msg)
  quickCheck' 1000 leftDistribution

  log ("Checking 'Right distribution' law for " <> msg)
  quickCheck' 1000 rightDistribution

  log ("Checking 'Annihilation' law for " <> msg)
  quickCheck' 1000 annihiliation

  where

  scalarFactor ∷ a -> GeoAlg a -> GeoAlg a -> Boolean
  scalarFactor s a b = (s *. a) `mult` b == a `mult` (s *. b)
    && (s *. a) `mult` b == s *. (a `mult` b)

  associativeGeoMult ∷ GeoAlg a -> GeoAlg a -> GeoAlg a -> Boolean
  associativeGeoMult a b c =
    (a `mult` b) `mult` c == a `mult` (b `mult` c)

  identityGeoMult ∷ GeoAlg a -> Boolean
  identityGeoMult a =
    (unit `mult` a == a) && (a `mult` unit == a)

  leftDistribution ∷ GeoAlg a -> GeoAlg a -> GeoAlg a -> Boolean
  leftDistribution a b c =
    a `mult` (b + c) == (a `mult` b) + (a `mult` c)

  rightDistribution ∷ GeoAlg a -> GeoAlg a -> GeoAlg a -> Boolean
  rightDistribution a b c =
    (a + b) `mult` c == (a `mult` c) + (b `mult` c)

  annihiliation ∷  GeoAlg a -> Boolean
  annihiliation a = (a `mult` zero == zero) && (zero `mult` a == zero)

checkDeMorgan :: forall a. Ring a => Eq a => Arbitrary a =>
  String ->
  (GeoAlg a -> GeoAlg a -> GeoAlg a) ->
  (GeoAlg a -> GeoAlg a -> GeoAlg a) ->
  Proxy (GeoAlg a) ->
  Effect Unit
checkDeMorgan msg mult revmult _ = do

  log ("Checking 'DeMorgan' left law for " <> msg)
  quickCheck' 1000 (deMorgan cmplL)

  log ("Checking 'DeMorgan' left reverse law for " <> msg)
  quickCheck' 1000 (deMorganRev cmplL)

  log ("Checking 'DeMorgan' right law for " <> msg)
  quickCheck' 1000 (deMorgan cmplR)

  log ("Checking 'DeMorgan' right reverse law for " <> msg)
  quickCheck' 1000 (deMorganRev cmplR)

  where

  deMorgan ∷
    (GeoAlg a -> GeoAlg a) ->
    GeoAlg a -> GeoAlg a -> Boolean
  deMorgan cmpl a b =
    cmpl (a `mult` b) == cmpl a `revmult` cmpl b

  deMorganRev ∷
    (GeoAlg a -> GeoAlg a) ->
    GeoAlg a -> GeoAlg a -> Boolean
  deMorganRev cmpl a b =
    cmpl (a `revmult` b) == cmpl a `mult` cmpl b

