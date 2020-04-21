{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.Dependent.Map.Merge
  (
    -- ** Simple merge tactic types
    SimpleWhenMissing
  , SimpleWhenMatched

  -- ** General combining function
  , merge

  -- *** @WhenMatched@ tactics
  , zipWithMaybeMatched
  , zipWithMatched

  -- *** @WhenMissing@ tactics
  , mapMaybeMissing
  , dropMissing
  , preserveMissing
  , mapMissing
  , filterMissing

  -- ** Applicative merge tactic types
  , WhenMissing
  , WhenMatched

  -- ** Applicative general combining function
  , mergeA

  -- *** @WhenMatched@ tactics
  -- | The tactics described for 'merge' work for
  -- 'mergeA' as well. Furthermore, the following
  -- are available.
  , zipWithMaybeAMatched
  , zipWithAMatched

  -- *** @WhenMissing@ tactics
  -- | The tactics described for 'merge' work for
  -- 'mergeA' as well. Furthermore, the following
  -- are available.
  , traverseMaybeMissing
  , traverseMissing
  , filterAMissing

  -- *** Covariant maps for tactics
  , mapWhenMissing
  , mapWhenMatched

  -- *** Contravariant maps for tactics
  , lmapWhenMissing
  , contramapFirstWhenMatched
  , contramapSecondWhenMatched

  -- *** Miscellaneous tactic functions
  , runWhenMatched
  , runWhenMissing
  ) where

import Data.GADT.Compare (GCompare)
import Control.Applicative (liftA3)
import Data.Functor.Identity
import Data.Dependent.Map.Internal

-- | A tactic for dealing with keys present in one map but not the other in
-- 'merge' or 'mergeA'.
--
-- A tactic of type @ WhenMissing f k g h @ is an abstract representation
-- of a function of type @ forall a. k a -> g a -> f (Maybe (h a)) @.
--
-- @since UNRELEASED
data WhenMissing f k x y = WhenMissing
  { missingSubtree :: DMap k x -> f (DMap k y)
  , missingKey :: forall a. k a -> x a -> f (Maybe (y a))
  }

-- | Map covariantly over a @'WhenMissing' f k x@.
--
-- @since UNRELEASED
mapWhenMissing
  :: (Applicative f, Monad f)
  => (forall a. g a -> h a)
  -> WhenMissing f k x g -> WhenMissing f k x h
mapWhenMissing f t = WhenMissing
    { missingSubtree = \m -> missingSubtree t m >>= \m' -> pure $! mapWithKey (\_ -> f) m'
    , missingKey = \k x -> missingKey t k x >>= \q -> (pure $! fmap f q) }
{-# INLINE mapWhenMissing #-}

-- | Map contravariantly over a @'WhenMissing' f k _ x@.
--
-- @since UNRELEASED
lmapWhenMissing :: (forall a. h a -> g a) -> WhenMissing f k g x -> WhenMissing f k h x
lmapWhenMissing f t = WhenMissing
  { missingSubtree = \m -> missingSubtree t (mapWithKey (const f) m)
  , missingKey = \k x -> missingKey t k (f x) }
{-# INLINE lmapWhenMissing #-}

-- | Map contravariantly over a @'WhenMatched' f k _ y z@.
--
-- @since UNRELEASED
contramapFirstWhenMatched
  :: (forall a. h a -> g a)
  -> WhenMatched f k g y z
  -> WhenMatched f k h y z
contramapFirstWhenMatched f t = WhenMatched $
  \k x y -> runWhenMatched t k (f x) y
{-# INLINE contramapFirstWhenMatched #-}

-- | Map contravariantly over a @'WhenMatched' f k x _ z@.
--
-- @since UNRELEASED
contramapSecondWhenMatched
  :: (forall a. h a -> g a)
  -> WhenMatched f k x g z
  -> WhenMatched f k x h z
contramapSecondWhenMatched f t = WhenMatched $
  \k x y -> runWhenMatched t k x (f y)
{-# INLINE contramapSecondWhenMatched #-}

-- | A tactic for dealing with keys present in one map but not the other in
-- 'merge'.
--
-- A tactic of type @ SimpleWhenMissing k x z @ is an abstract representation
-- of a function of type @ forall a. k a -> x a -> Maybe (z a) @.
--
-- @since UNRELEASED
type SimpleWhenMissing = WhenMissing Identity

newtype WhenMatched f k x y z = WhenMatched
  { matchedKey :: forall a. k a -> x a -> y a -> f (Maybe (z a))
  }

-- | Along with zipWithMaybeAMatched, witnesses the isomorphism between
-- @WhenMatched f k x y z@ and @forall a. k a -> x a -> y a -> f (Maybe (z a))@.
--
-- @since UNRELEASED
runWhenMatched :: WhenMatched f k x y z -> k a -> x a -> y a -> f (Maybe (z a))
runWhenMatched = matchedKey
{-# INLINE runWhenMatched #-}

-- | Along with traverseMaybeMissing, witnesses the isomorphism between
-- @WhenMissing f k x y@ and @forall a. k a -> x a -> f (Maybe (y a))@.
--
-- @since UNRELEASED
runWhenMissing :: WhenMissing f k x y -> k a -> x a -> f (Maybe (y a))
runWhenMissing = missingKey
{-# INLINE runWhenMissing #-}

-- | Map covariantly over a @'WhenMatched' f k x y@.
--
-- @since UNRELEASED
mapWhenMatched
  :: Functor f
  => (forall a. g a -> h a)
  -> WhenMatched f k x y g
  -> WhenMatched f k x y h
mapWhenMatched f (WhenMatched g) = WhenMatched $ \k x y -> fmap (fmap f) (g k x y)
{-# INLINE mapWhenMatched #-}

-- | A tactic for dealing with keys present in both maps in 'merge'.
--
-- A tactic of type @ SimpleWhenMissing k x z @ is an abstract representation
-- of a function of type @ forall a. k a -> x a -> Maybe (z a) @.
--
-- @since UNRELEASED
type SimpleWhenMatched = WhenMatched Identity

-- | When a key is found in both maps, apply a function to the
-- key and values and use the result in the merged map.
--
-- @
-- zipWithMatched :: (forall a. k a -> x a -> y a -> z a)
--                -> SimpleWhenMatched k x y z
-- @
--
-- @since UNRELEASED
zipWithMatched
  :: Applicative f
  => (forall a. k a -> x a -> y a -> z a)
  -> WhenMatched f k x y z
zipWithMatched f = WhenMatched $ \ k x y -> pure . Just $ f k x y
{-# INLINE zipWithMatched #-}

-- | When a key is found in both maps, apply a function to the
-- key and values to produce an action and use its result in the merged map.
--
-- @since UNRELEASED
zipWithAMatched
  :: Applicative f
  => (forall a. k a -> x a -> y a -> f (z a))
  -> WhenMatched f k x y z
zipWithAMatched f = WhenMatched $ \ k x y -> Just <$> f k x y
{-# INLINE zipWithAMatched #-}

-- | When a key is found in both maps, apply a function to the
-- key and values and maybe use the result in the merged map.
--
-- @
-- zipWithMaybeMatched :: (forall a. k a -> x a -> y a -> Maybe (z a))
--                     -> SimpleWhenMatched k x y z
-- @
--
-- @since UNRELEASED
zipWithMaybeMatched
  :: Applicative f
  => (forall a. k a -> x a -> y a -> Maybe (z a))
  -> WhenMatched f k x y z
zipWithMaybeMatched f = WhenMatched $ \ k x y -> pure $ f k x y
{-# INLINE zipWithMaybeMatched #-}

-- | When a key is found in both maps, apply a function to the
-- key and values, perform the resulting action, and maybe use
-- the result in the merged map.
--
-- This is the fundamental 'WhenMatched' tactic.
--
-- @since UNRELEASED
zipWithMaybeAMatched
  :: (forall a. k a -> x a -> y a -> f (Maybe (z a)))
  -> WhenMatched f k x y z
zipWithMaybeAMatched f = WhenMatched $ \ k x y -> f k x y
{-# INLINE zipWithMaybeAMatched #-}


-- | Drop all the entries whose keys are missing from the other
-- map.
--
-- @
-- dropMissing :: SimpleWhenMissing k x y
-- @
--
-- prop> dropMissing = mapMaybeMissing (\_ _ -> Nothing)
--
-- but @dropMissing@ is much faster.
--
-- @since UNRELEASED
dropMissing :: Applicative f => WhenMissing f k x y
dropMissing = WhenMissing
  { missingSubtree = const (pure Tip)
  , missingKey = \_ _ -> pure Nothing }
{-# INLINE dropMissing #-}

-- | Preserve, unchanged, the entries whose keys are missing from
-- the other map.
--
-- @
-- preserveMissing :: SimpleWhenMissing k x x
-- @
--
-- prop> preserveMissing = Merge.Lazy.mapMaybeMissing (\_ x -> Just x)
--
-- but @preserveMissing@ is much faster.
--
-- @since UNRELEASED
preserveMissing :: Applicative f => WhenMissing f k x x
preserveMissing = WhenMissing
  { missingSubtree = pure
  , missingKey = \_ v -> pure (Just v) }
{-# INLINE preserveMissing #-}

-- | Map over the entries whose keys are missing from the other map.
--
-- @
-- mapMissing :: (forall a. k a -> x a -> y a) -> SimpleWhenMissing k x y
-- @
--
-- prop> mapMissing f = mapMaybeMissing (\k x -> Just $ f k x)
--
-- but @mapMissing@ is somewhat faster.
--
-- @since UNRELEASED
mapMissing :: Applicative f => (forall a. k a -> x a -> y a) -> WhenMissing f k x y
mapMissing f = WhenMissing
  { missingSubtree = \m -> pure $! mapWithKey f m
  , missingKey = \ k x -> pure $ Just (f k x) }
{-# INLINE mapMissing #-}

-- | Map over the entries whose keys are missing from the other map,
-- optionally removing some. This is the most powerful 'SimpleWhenMissing'
-- tactic, but others are usually more efficient.
--
-- @
-- mapMaybeMissing :: (forall a. k a -> x a -> Maybe (y a)) -> SimpleWhenMissing k x y
-- @
--
-- prop> mapMaybeMissing f = traverseMaybeMissing (\k x -> pure (f k x))
--
-- but @mapMaybeMissing@ uses fewer unnecessary 'Applicative' operations.
--
-- @since UNRELEASED
mapMaybeMissing :: (GCompare k, Applicative f) => (forall a. k a -> x a -> Maybe (y a)) -> WhenMissing f k x y
mapMaybeMissing f = WhenMissing
  { missingSubtree = \m -> pure $! mapMaybeWithKey f m
  , missingKey = \k x -> pure $! f k x }
{-# INLINE mapMaybeMissing #-}

-- | Filter the entries whose keys are missing from the other map.
--
-- @
-- filterMissing :: (forall a. k a -> x a -> Bool) -> SimpleWhenMissing k x x
-- @
--
-- prop> filterMissing f = Merge.Lazy.mapMaybeMissing $ \k x -> guard (f k x) *> Just x
--
-- but this should be a little faster.
--
-- @since UNRELEASED
filterMissing
  :: (GCompare k, Applicative f)
  => (forall a. k a -> x a -> Bool) -> WhenMissing f k x x
filterMissing f = WhenMissing
  { missingSubtree = \m -> pure $! filterWithKey f m
  , missingKey = \k x -> pure $! if f k x then Just x else Nothing }
{-# INLINE filterMissing #-}

-- | Filter the entries whose keys are missing from the other map
-- using some 'Applicative' action.
--
-- @
-- filterAMissing f = Merge.Lazy.traverseMaybeMissing $
--   \k x -> (\b -> guard b *> Just x) <$> f k x
-- @
--
-- but this should be a little faster.
--
-- @since UNRELEASED
filterAMissing
  :: (GCompare k, Applicative f)
  => (forall a. k a -> x a -> f Bool) -> WhenMissing f k x x
filterAMissing f = WhenMissing
  { missingSubtree = \m -> filterWithKeyA f m
  , missingKey = \k x -> bool Nothing (Just x) <$> f k x }
{-# INLINE filterAMissing #-}

-- | This wasn't in Data.Bool until 4.7.0, so we define it here
bool :: a -> a -> Bool -> a
bool f _ False = f
bool _ t True  = t

-- | Traverse over the entries whose keys are missing from the other map.
--
-- @since UNRELEASED
traverseMissing
  :: Applicative f
  => (forall a. k a -> x a -> f (y a)) -> WhenMissing f k x y
traverseMissing f = WhenMissing
  { missingSubtree = traverseWithKey f
  , missingKey = \k x -> Just <$> f k x }
{-# INLINE traverseMissing #-}

-- | Traverse over the entries whose keys are missing from the other map,
-- optionally producing values to put in the result.
-- This is the most powerful 'WhenMissing' tactic, but others are usually
-- more efficient.
--
-- @since UNRELEASED
traverseMaybeMissing
  :: (GCompare k, Applicative f)
  => (forall a. k a -> x a -> f (Maybe (y a))) -> WhenMissing f k x y
traverseMaybeMissing f = WhenMissing
  { missingSubtree = traverseMaybeWithKey f
  , missingKey = f }
{-# INLINE traverseMaybeMissing #-}

merge :: GCompare k
  => SimpleWhenMissing k a c -- ^ What to do with keys in @m1@ but not @m2@
  -> SimpleWhenMissing k b c -- ^ What to do with keys in @m2@ but not @m1@
  -> SimpleWhenMatched k a b c -- ^ What to do with keys in both @m1@ and @m2@
  -> DMap k a -- ^ DMap @m1@
  -> DMap k b -- ^ DMap @m2@
  -> DMap k c
merge g1 g2 f m1 m2 = runIdentity $ mergeA g1 g2 f m1 m2

mergeA
  :: (Applicative f, GCompare k)
  => WhenMissing f k a c -- ^ What to do with keys in @m1@ but not @m2@
  -> WhenMissing f k b c -- ^ What to do with keys in @m2@ but not @m1@
  -> WhenMatched f k a b c -- ^ What to do with keys in both @m1@ and @m2@
  -> DMap k a -- ^ DMap @m1@
  -> DMap k b -- ^ DMap @m2@
  -> f (DMap k c)
mergeA
    WhenMissing{missingSubtree = g1t, missingKey = g1k}
    WhenMissing{missingSubtree = g2t}
    (WhenMatched f) = go
  where
    go t1 Tip = g1t t1
    go Tip t2 = g2t t2
    go (Bin _ kx x1 l1 r1) t2 = case splitLookup kx t2 of
      (l2, mx2, r2) -> case mx2 of
          Nothing -> liftA3 (\l' mx' r' -> maybe link2 (combine kx) mx' l' r')
                        l1l2 (g1k kx x1) r1r2
          Just x2 -> liftA3 (\l' mx' r' -> maybe link2 (combine kx) mx' l' r')
                        l1l2 (f kx x1 x2) r1r2
        where
          !l1l2 = go l1 l2
          !r1r2 = go r1 r2
{-# INLINE mergeA #-}
