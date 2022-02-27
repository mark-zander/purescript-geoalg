module Data.GeoAlgFcn
  ( (*.)
  , (-|)
  , (/.\)
  , (/\)
  , (=|)
  , (\/)
  , (|-)
  , (|=)
  , adot
  , antiExt
  , antiIntrL
  , antiIntrR
  , antigrade
  , arev
  , bulk
  , bulkNorm
  , cmplD
  , cmplL
  , cmplR
  , dot
  , geoExt
  , geoMult
  , geoNorm
  , geoProp
  , grade
  , intrMultL
  , intrMultR
  , isUnitized
  , rev
  , scalarMult
  , sel
  , unitize
  , wght
  , wghtNorm
  )
  where

import ZPrelude

import Data.GeoAlgType
import Data.GeoTables
import Data.GeoElem

import Math as Math
import Data.Number.Approximate ((~=))

-- Needed tables converted from `Array` to `ArrayIx` for 2D multiply
-- tables and from `Array` to `GeoAlg` for 1D tables.
gpTblIx = ixixTbl gpTbl :: GeoAlg (GeoAlg TblEntry)

grdTblIx = ixTbl grdTbl :: GeoAlg Int

cmplRTblGeo = ixTbl cmplRTbl :: GeoAlg TblEntry

cmplLTblGeo = ixTbl cmplLTbl :: GeoAlg TblEntry

cmplDTblGeo = ixTbl cmplDTbl :: GeoAlg Sign

revTblGeo = ixTbl revTbl :: GeoAlg Sign

revATblGeo = ixTbl revATbl :: GeoAlg Sign

dotTblGeo = ixTbl dotTbl :: GeoAlg TblEntry

dotATblGeo = ixTbl dotATbl :: GeoAlg TblEntry

blkTblGeo = ixTbl blkTbl :: GeoAlg Sign

wghtTblGeo = ixTbl wghtTbl :: GeoAlg Sign

-- Multiplication funtions
geoMult :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
geoMult = gMultiply gpTblIx interpGeo

infixl 7 geoMult as /.\

geoExt :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
geoExt = gMultiply gpTblIx interpExt

infixl 7 geoExt as /\

antiExt :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
antiExt = gMultiply gapTblIx interpExt

infixl 7 antiMult as \/

intrMultL :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
intrMultL a b = gMultiply gpTblIx interpExt (cmplL a) b

infixl 7 intrMultL as -|

intrMultR :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
intrMultR a b = gMultiply gpTblIx interpExt a (cmplR b)

infixl 7 intrMultR as |-

antiIntrL :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
antiIntrL a b = gMultiply gapTblIx interpExt (cmplL a) b

infixl 7 antiIntrL as =|

antiIntrR :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
antiIntrR a b = gMultiply gapTblIx interpExt a (cmplR b)

infixl 7 antiIntrR as |=

scalarMult :: forall a. Semiring a => a -> GeoAlg a -> GeoAlg a
scalarMult s xs = map (s * _) xs

infix 7 scalarMult as *.

-- Grade
grade :: Element -> Int
grade e = grdTblIx !! e

-- Antigrade
antigrade :: Element -> Int
antigrade e = 4 - grdTblIx !! e

-- Bulk - solid dot subscript
bulk :: forall a. Ring a => GeoAlg a -> GeoAlg a
bulk xs = zipWithGeo sel blkTblGeo xs

-- Weight - hollow dot subscript
wght :: forall a. Ring a => GeoAlg a -> GeoAlg a
wght xs = zipWithGeo sel wghtTblGeo xs

sel :: forall a. Ring a => Sign -> a -> a
sel flag x = case flag of
  Plus -> x
  Zero -> zero
  Neg  -> negate x

-- Left compliment - bar below
cmplL :: forall a. Ring a => GeoAlg a -> GeoAlg a
cmplL xs = gUniOp cmplLTblGeo xs

-- Right compliment - bar above
cmplR :: forall a. Ring a => GeoAlg a -> GeoAlg a
cmplR xs = gUniOp cmplRTblGeo xs

-- Double complement - double bar top == double bar bottom
cmplD :: forall a. Ring a => GeoAlg a -> GeoAlg a
cmplD = zipWithGeo sel cmplDTblGeo

-- Geometric Algebra reverse - tilda above
rev :: forall a. Ring a => GeoAlg a -> GeoAlg a
rev xs = zipWithGeo sel revTblGeo xs

-- Geometric Algebra antireverse - tilda below
arev :: forall a. Ring a => GeoAlg a -> GeoAlg a
arev xs = zipWithGeo sel revATblGeo xs

-- Dot product - solid dot binary operator
dot :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
dot xs ys = gUniOp dotTblGeo <| zipWithGeo (*) xs ys

-- Antidot product - hollow dot binary operator
adot :: forall a. Ring a => GeoAlg a -> GeoAlg a -> GeoAlg a
adot xs ys = gUniOp dotATblGeo <| zipWithGeo (*) xs ys

-- Geometric property determines if a value of Geometric Algebra
-- is displayable. We are only interested in the set of Geometric
-- Algebra that is displayable.
geoProp :: forall a. Ring a => Eq a => GeoAlg a -> Boolean
geoProp xs = xs /.\ rev xs == xs `dot` rev xs &&
  xs \./ arev xs == xs `adot` arev xs

-- Bulk Norm - || a || with solid dot subscript
-- Should be a PGA scalar, returns just a number instead
bulkNorm :: GeoAlg Number -> Number
bulkNorm xs = Math.sqrt ((xs `dot` (rev xs)) !! E)
-- bulkNorm xs = Math.sqrt <$> (xs `dot` (rev xs))
-- bulkNorm xs = updateAt E  (Math.sqrt ((xs `dot` (rev xs)) !! E)) zero

-- Weight Norm - || a || with hollow dot subscript
-- Should be a PGA antiscalar, returns just a number instead
wghtNorm :: GeoAlg Number -> Number
wghtNorm xs = Math.sqrt ((xs `adot` (arev xs)) !! E1234)
-- wghtNorm xs = Math.sqrt <$> (xs `adot` (arev xs))
--  updateAt E1234  (Math.sqrt ((xs `adot` (arev xs)) !! E1234)) zero

-- Unitized Geometric Norm - || a ||
-- Should be a PGA scalar and a unit antiscalar, returns just a number
geoNorm :: GeoAlg Number -> Number
geoNorm xs = bulkNorm xs / wghtNorm xs

isUnitized :: GeoAlg Number -> Boolean
isUnitized xs = wghtNorm xs ~= 1.0

-- Unitization - hat above
-- Check for |wghtNorm - 1| < epsilon 
unitize :: GeoAlg Number -> GeoAlg Number
unitize xs = let unit = wghtNorm xs in
  if unit ~= 1.0 || unit ~= 0.0 then xs
  else map (_ / unit) xs
-- unitize xs = map f xs where
--   w = wghtNorm xs !! E1234
--   f x = x / w

-- Commutators
commute :: (GeoAlg Number -> GeoAlg Number -> GeoAlg Number)
  -> (GeoAlg Number -> GeoAlg Number -> GeoAlg Number)
  -> GeoAlg Number -> GeoAlg Number -> GeoAlg Number
commute mulop addop xs ys =
  map (0.5 * _) ((xs `mulop` ys) `addop` (ys `mulop` xs))
