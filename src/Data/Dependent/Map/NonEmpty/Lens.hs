{-# LANGUAGE CPP #-}
-- |
-- Some functions for using lenses with 'NonEmptyDMap'.
module Data.Dependent.Map.NonEmpty.Lens
  ( -- * At
    dmat
    -- * Ix
  , dmix
  )
  where

import           Prelude             hiding (lookup)

#if !MIN_VERSION_base(4,8,0)
import           Control.Applicative (Applicative (pure))
#endif

import           Data.Dependent.Map.NonEmpty (NonEmptyDMap, adjustF, alterF)

import           Data.GADT.Compare   (GCompare)

-- |
-- These functions have been specialised for use with 'NonEmptyDMap' but without any of the
-- specific 'lens' types used so that we have compatilibity without needing the
-- dependency just for these functions.
--

-- |
-- This is equivalent to the <https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-At.html#v:at at> <https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-Type.html#t:Lens-39- Lens'> from <https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-At.html Control.Lens.At>:
--
-- @
-- type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
--
-- at :: Index m -> Lens' m (Maybe (IxValue m))
-- @
--
-- So the type of 'dmat' is equivalent to:
--
-- @
-- dmat :: GCompare k => Lens' (NonEmptyDMap k f) (Maybe (f v))
-- @
--
-- >>> NonEmptyDMap.fromList [AInt :=> Identity 33, AFloat :=> Identity 3.5] & dmat AString ?~ "Hat"
-- NonEmptyDMap.fromList [AString :=> Identity "Hat", AInt :=> Identity 33, AFloat :=> Identity 3.5]
--
-- >>> NonEmptyDMap.fromList [AString :=> Identity "Shoe", AInt :=> Identity 33, AFloat :=> Identity 3.5] ^? dmat AFloat
-- Just (AFloat :=> 3.5)
--
dmat :: (GCompare k, Functor f) => k v -> (Maybe (g v) -> f (Maybe (g v))) -> NonEmptyDMap k g -> f (Maybe (NonEmptyDMap k g))
dmat k f = alterF k f
{-# INLINE dmat #-}

-- |
-- This is equivalent to the <https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-At.html#v:ix ix> <https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-Type.html#t:Traversal-39- Traversal'> from <https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-At.html Control.Lens.At>:
--
-- @
-- type Traversal s t a b = forall f. Applicative f => (a -> f b) -> s -> f t
--
-- ix :: Index m -> Traversal' m (IxValue m)
-- @
--
-- So the type of 'dmix' is equivalent to:
--
-- @
-- dmix :: GCompare k => k v -> Traversal' (NonEmptyDMap k f) (f v)
-- @
--
-- /NB:/ Setting the value of this
-- <https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-Type.html#t:Traversal Traversal>
-- will only set the value in 'dmix' if it is already present.
--
-- If you want to be able to insert /missing/ values, you want 'dmat'.
--
-- >>> NonEmptyDMap.fromList [AString :=> Identity "Shoe", AInt :=> Identity 33, AFloat :=> Identity 3.5] & dmix AInt %~ f
-- NonEmptyDMap.fromList [AString :=> Identity "Shoe", AInt :=> Identity (f 33), AFloat :=> Identity 3.5]
--
-- >>> NonEmptyDMap.fromList [AString :=> Identity "Shoe", AInt :=> Identity 33, AFloat :=> Identity 3.5] & dmix AString .~ "Hat"
-- NonEmptyDMap.fromList [AString :=> Identity "Hat", AInt :=> Identity 33, AFloat :=> Identity 3.5]
--
-- >>> NonEmptyDMap.fromList [AString :=> Identity "Shoe", AInt :=> Identity 33, AFloat :=> Identity 3.5] ^? dmix AFloat
-- Just (AFloat :=> 3.5)
--
-- >>> NonEmptyDMap.fromList [AString :=> Identity "Shoe", AFloat :=> Identity 3.5] ^? dmix AInt
-- Nothing
dmix :: (GCompare k, Applicative f) => k v -> (g v -> f (g v)) -> NonEmptyDMap k g -> f (NonEmptyDMap k g)
dmix = adjustF
{-# INLINE dmix #-}
