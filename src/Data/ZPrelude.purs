module ZPrelude
  ( (//)
  , (<<)
  , (<|)
  , (>>)
  , (|>)
  , fromChoice
  , id
  , minus
  , module ReExports
  , sq
  )
  where

import Control.Semigroupoid (compose, composeFlipped)
import Data.Function (apply, applyFlipped, flip, const)
import Prelude as ReExports
import Data.Foldable
import Data.Ring

-- from Paxl.Prelude
infixr 0 apply as <|
infixl 1 applyFlipped as |>
infixr 9 compose as <<
infixl 9 composeFlipped as >>

-- Combines fromMaybe and fromRight with arguments reversed.
-- from: https://danso.ca/blog/frommaybe-is-just-a-fold/#fn1
fromChoice :: forall a f. Foldable f => f a -> a -> a
fromChoice = flip (foldr const)
infix 0 fromChoice as //

sq :: forall a. ReExports.Semiring a => a -> a
sq x = ReExports.mul x x

id :: forall c t. ReExports.Category c => c t t
id = ReExports.identity

minus :: forall a. Ring a => a -> a -> a
minus x y = sub y x
