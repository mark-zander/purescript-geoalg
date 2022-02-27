module Data.GeoTables
  ( Sign(..)
  , TblEntry(..)
  , blkTbl
  , cmplDTbl
  , cmplLTbl
  , cmplRTbl
  , dotATbl
  , dotTbl
  , gapTbl
  , gpTbl
  , grdTbl
  , revATbl
  , revTbl
  , wghtTbl
  )
  where

import Data.GeoElem


data TblEntry
    = Z                 -- | Zero, no product
    | P Element         -- | Positive product
    | N Element         -- | Negative product
    | XP Element        -- | Exterior and Geometric
    | XN Element        -- | Ext and Geo

data Sign = Plus | Zero | Neg

-- | Geometric Product Table
gpTbl :: A16 (A16 TblEntry)
gpTbl = A16
  (A16 (XP E)     (XP E1) (XP E2) (XP E3) (XP E4)    (XP E23) (XP E31) (XP E12) (XP E43) (XP E42) (XP E41)  (XP E321) (XP E124) (XP E314) (XP E234) (XP E1234))

  (A16 (XP E1)    (P E) (XP E12) (XN E31) (XN E41)   (XN E321) (N E3) (P E2) (XP E314) (XN E124) (N E4)     (N E23) (N E42) (P E43) (XP E1234)      (P E234))
  (A16 (XP E2)    (XN E12) (P E) (XP E23) (XN E42)   (P E3) (XN E321) (N E1) (XN E234) (N E4) (XP E124)     (N E31) (P E41) (XP E1234) (N E43)      (P E314))
  (A16 (XP E3)    (XP E31) (XN E23) (P E) (XN E43)   (N E2) (P E1) (XN E321) (N E4) (XP E234) (XN E314)     (N E12) (XP E1234) (N E41) (P E42)      (P E124))
  (A16 (XP E4)    (XP E41) (XP E42) (XP E43)  Z      (XP E234) (XP E314) (XP E124)  Z  Z  Z                 (XP E1234)  Z  Z  Z                     Z)

  (A16 (XP E23)   (XN E321) (N E3) (P E2) (XP E234)  (N E) (N E12) (P E31) (P E42) (N E43) (XN E1234)       (P E1) (P E314) (N E124) (N E4)         (P E41))
  (A16 (XP E31)   (P E3) (XN E321) (N E1) (XP E314)  (P E12) (N E) (N E23) (N E41) (XN E1234) (P E43)       (P E2) (N E234) (N E4) (P E124)         (P E42))
  (A16 (XP E12)   (N E2) (P E1) (XN E321) (XP E124)  (N E31) (P E23) (N E) (XN E1234) (P E41) (N E42)       (P E3) (N E4) (P E234) (N E314)         (P E43))
  (A16 (XP E43)   (XP E314) (XN E234) (P E4)  Z      (N E42) (P E41) (XN E1234)  Z  Z  Z                    (N E124)  Z  Z  Z                       Z)
  (A16 (XP E42)   (XN E124) (P E4) (XP E234)  Z      (P E43) (XN E1234) (N E41)  Z  Z  Z                    (N E314)  Z  Z  Z                       Z)
  (A16 (XP E41)   (P E4) (XP E124) (XN E314)  Z      (XN E1234) (N E43) (P E42)  Z  Z  Z                    (N E234)  Z  Z  Z                       Z)

  (A16 (XP E321)  (N E23) (N E31) (N E12) (XN E1234) (P E1) (P E2) (P E3) (P E124) (P E314) (P E234)        (N E) (N E43) (N E42) (N E41)           (P E4))
  (A16 (XP E124)  (N E42) (P E41) (XN E1234)  Z      (N E314) (P E234) (N E4)  Z  Z  Z                      (P E43)  Z  Z  Z                        Z)
  (A16 (XP E314)  (P E43) (XN E1234) (N E41)  Z      (P E124) (N E4) (N E234)  Z  Z  Z                      (P E42)  Z  Z  Z                        Z)
  (A16 (XP E234)  (XN E1234) (N E43) (P E42)  Z      (N E4) (N E124) (P E314)  Z  Z  Z                      (P E41)  Z  Z  Z                        Z)

  (A16 (XP E1234) (N E234) (N E314) (N E124)  Z      (P E41) (P E42) (P E43)  Z  Z  Z                       (N E4)  Z  Z  Z                         Z)

-- | Geometric Anti Product Table
gapTbl :: A16 (A16 TblEntry)
gapTbl = A16
  (A16 Z          Z Z Z (P E321)                     Z Z Z (P E12) (P E31) (P E23)                          Z (P E3) (P E2) (P E1)                  (XP E))

  (A16 Z          Z Z Z (N E23)                      Z Z Z (N E2) (P E3) (N E321)                           Z (P E31) (N E12) (XP E)                (XP E1))
  (A16 Z          Z Z Z (N E31)                      Z Z Z (P E1) (N E321) (N E3)                           Z (N E23) (XP E) (P E12)                (XP E2))
  (A16 Z          Z Z Z (N E12)                      Z Z Z (N E321) (N E1) (P E2)                           Z (XP E) (P E23) (N E31)                (XP E3))
  (A16 (N E321)   (P E23) (P E31) (P E12) (N E1234)  (N E1) (N E2) (N E3) (P E124) (P E314) (P E234)        (XP E) (N E43) (N E42) (N E41)          (XP E4))

  (A16 Z          Z Z Z (P E1)                       Z Z Z (N E31) (P E12) (XN E)                           Z (XN E2) (XP E3) (N E321)              (XP E23))
  (A16 Z          Z Z Z (P E2)                       Z Z Z (P E23) (XN E) (N E12)                           Z (XP E1) (N E321) (XN E3)              (XP E31))
  (A16 Z          Z Z Z (P E3)                       Z Z Z (XN E) (N E23) (P E31)                           Z (N E321) (XN E1) (XP E2)              (XP E12))
  (A16 (P E12)    (P E2) (N E1) (N E321) (P E124)    (P E31) (N E23) (XN E) (N E1234) (N E41) (P E42)       (XP E3) (XN E4) (N E234) (P E314)       (XP E43))
  (A16 (P E31)    (N E3) (N E321) (P E1) (P E314)    (N E12) (XN E) (P E23) (P E41) (N E1234) (N E43)       (XP E2) (P E234) (XN E4) (N E124)       (XP E42))
  (A16 (P E23)    (N E321) (P E3) (N E2) (P E234)    (XN E) (P E12) (N E31) (N E42) (P E43) (N E1234)       (XP E1) (N E314) (P E124) (XN E4)       (XP E41))

  (A16 Z          Z Z Z (XN E)                       Z Z Z (XP E3) (XP E2) (XP E1)                          Z (XN E12) (XN E31) (XN E23)            (XP E321))
  (A16 (N E3)     (P E31) (N E23) (XN E) (N E43)     (XN E2) (XP E1) (P E321) (XN E4) (N E234) (P E314)     (XP E12) (P E1234) (XP E41) (XN E42)   (XP E124))
  (A16 (N E2)     (N E12) (XN E) (P E23) (N E42)     (XP E3) (P E321) (XN E1) (P E234) (XN E4) (N E124)     (XP E31) (XN E41) (P E1234) (XP E43)   (XP E314))
  (A16 (N E1)     (XN E) (P E12) (N E31) (N E41)     (P E321) (XN E3) (XP E2) (N E314) (P E124) (XN E4)     (XP E23) (XP E42) (XN E43) (P E1234)   (XP E234))

  (A16 (XP E)     (XP E1) (XP E2) (XP E3) (XP E4)    (XP E23) (XP E31) (XP E12) (XP E43) (XP E42) (XP E41)  (XP E321) (XP E124) (XP E314) (XP E234) (XP E1234))

-- | Grade Table
grdTbl :: A16 Int
grdTbl =  A16 0 1 1 1 1 2 2 2 2 2 2 3 3 3 3 4

-- | Complement Right Table
cmplRTbl :: A16 TblEntry
cmplRTbl =  A16 (P E1234) (P E234) (P E314) (P E124) (P E321) (N E41) (N E42) (N E43) (N E12) (N E31) (N E23) (N E4) (N E3) (N E2) (N E1) (P E)

-- | Complement Left Table
cmplLTbl :: A16 TblEntry
cmplLTbl =  A16 (P E1234) (N E234) (N E314) (N E124) (N E321) (N E41) (N E42) (N E43) (N E12) (N E31) (N E23) (P E4) (P E3) (P E2) (P E1) (P E)

-- | Complement Double Table
cmplDTbl :: A16 Sign
cmplDTbl =  A16 Plus Neg Neg Neg Neg Plus Plus Plus Plus Plus Plus Neg Neg Neg Neg Plus

-- | Geometric Reverse Table
revTbl :: A16 Sign
revTbl =  A16 Plus Plus Plus Plus Plus Neg Neg Neg Neg Neg Neg Neg Neg Neg Neg Plus

-- | Geometric Reverse Anti Table
revATbl :: A16 Sign
revATbl =  A16 Plus Neg Neg Neg Neg Neg Neg Neg Neg Neg Neg Plus Plus Plus Plus Plus

-- | Dot Product Table
dotTbl :: A16 TblEntry
dotTbl =  A16 (P E) (P E) (P E) (P E) Z (N E) (N E) (N E) Z Z Z (N E) Z Z Z Z

-- | Dot Anti Product Table
dotATbl :: A16 TblEntry
dotATbl =  A16 Z Z Z Z (N E1234) Z Z Z (N E1234) (N E1234) (N E1234) Z (P E1234) (P E1234) (P E1234) (P E1234)

-- | Bulk Table
blkTbl :: A16 Sign
blkTbl =  A16 Plus Plus Plus Plus Zero Plus Plus Plus Zero Zero Zero Plus Zero Zero Zero Zero

-- | Weight Table, is the reverse or opposite of the Bulk Table
wghtTbl :: A16 Sign
wghtTbl =  A16 Zero Zero Zero Zero Plus Zero Zero Zero Plus Plus Plus Zero Plus Plus Plus Plus
