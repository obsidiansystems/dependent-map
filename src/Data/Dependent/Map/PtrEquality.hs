{-# LANGUAGE MagicHash #-}

{-# OPTIONS_HADDOCK hide #-}

-- | Really unsafe pointer equality
--
-- = WARNING
--
-- This module is considered __internal__.
--
-- The Package Versioning Policy __does not apply__.
--
-- The contents of this module may change __in any way whatsoever__
-- and __without any warning__ between minor versions of this package.
--
-- Authors importing this module are expected to track development
-- closely.

module Data.Dependent.Map.PtrEquality (ptrEq, hetPtrEq) where

import Unsafe.Coerce (unsafeCoerce)
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)


-- | Checks if two pointers are equal. Yes means yes;
-- no means maybe. The values should be forced to at least
-- WHNF before comparison to get moderately reliable results.
ptrEq :: a -> a -> Bool

-- | Checks if two pointers are equal, without requiring
-- them to have the same type. The values should be forced
-- to at least WHNF before comparison to get moderately
-- reliable results.
hetPtrEq :: a -> b -> Bool

ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)
hetPtrEq x y = isTrue# (unsafeCoerce reallyUnsafePtrEquality# x y)

{-# INLINE ptrEq #-}
{-# INLINE hetPtrEq #-}

infix 4 `ptrEq`
infix 4 `hetPtrEq`
