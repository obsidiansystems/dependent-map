{-# LANGUAGE GADTs, RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
#endif
module Data.Dependent.Map
    ( DMap
    , DSum(..), Some(..)
    , GCompare(..), GOrdering(..)

    -- * Operators
    , (!), (\\)

    -- * Query
    , null
    , size
    , member
    , notMember
    , lookup
    , findWithDefault

    -- * Construction
    , empty
    , singleton

    -- ** Insertion
    , insert
    , insertWith
    , insertWith'
    , insertWithKey
    , insertWithKey'
    , insertLookupWithKey
    , insertLookupWithKey'

    -- ** Delete\/Update
    , delete
    , adjust
    , adjustF
    , adjustWithKey
    , adjustWithKey'
    , update
    , updateWithKey
    , updateLookupWithKey
    , alter
    , alterF

    -- * Combine

    -- ** Union
    , union
    , unionWithKey
    , unions
    , unionsWithKey

    -- ** Difference
    , difference
    , differenceWithKey

    -- ** Intersection
    , intersection
    , intersectionWithKey

    -- * Traversal
    -- ** Map
    , map
    , mapWithKey
    , traverseWithKey
    , mapAccumLWithKey
    , mapAccumRWithKey
    , mapKeysWith
    , mapKeysMonotonic

    -- ** Fold
    , foldWithKey
    , foldrWithKey
    , foldlWithKey
    -- , foldlWithKey'

    -- * Conversion
    , keys
    , assocs

    -- ** Lists
    , toList
    , fromList
    , fromListWithKey

    -- ** Ordered lists
    , toAscList
    , toDescList
    , fromAscList
    , fromAscListWithKey
    , fromDistinctAscList

    -- * Filter
    , filter
    , filterWithKey
    , partitionWithKey

    , mapMaybe
    , mapMaybeWithKey
    , mapEitherWithKey

    , split
    , splitLookup

    -- * Submap
    , isSubmapOf, isSubmapOfBy
    , isProperSubmapOf, isProperSubmapOfBy

    -- * Indexed
    , lookupIndex
    , findIndex
    , elemAt
    , updateAt
    , deleteAt

    -- * Min\/Max
    , findMin
    , findMax
    , lookupMin
    , lookupMax
    , deleteMin
    , deleteMax
    , deleteFindMin
    , deleteFindMax
    , updateMinWithKey
    , updateMaxWithKey
    , minViewWithKey
    , maxViewWithKey

    -- * Debugging
    , showTree
    , showTreeWith
    , valid
    ) where

import Prelude hiding (null, lookup, map)
import qualified Prelude
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative(..), (<$>))
#endif
import Data.Dependent.Map.Internal
import Data.Dependent.Map.Internal2
#if !MIN_VERSION_base(4,7,0)
import Data.Dependent.Map.Typeable ({- instance Typeable ... -})
#endif

import Data.Dependent.Sum
import Data.Constraint.Extras
import Data.GADT.Compare
import Data.GADT.Show
import Data.Maybe (isJust)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif
import Data.Semigroup
import Data.Some
import Text.Read

instance (GCompare k) => Monoid (DMap k f) where
    mempty  = empty
    mappend = union
    mconcat = unions

instance (GCompare k) => Semigroup (DMap k f) where
  (<>) = mappend

{--------------------------------------------------------------------
  Operators
--------------------------------------------------------------------}
infixl 9 !,\\ --

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.
--
-- > fromList [(5,'a'), (3,'b')] ! 1    Error: element not in the map
-- > fromList [(5,'a'), (3,'b')] ! 5 == 'a'

(!) :: GCompare k => DMap k f -> k v -> f v
(!) m k    = find k m

-- | Same as 'difference'.
(\\) :: GCompare k => DMap k f -> DMap k f -> DMap k f
m1 \\ m2 = difference m1 m2

-- #if __GLASGOW_HASKELL__
--
-- {--------------------------------------------------------------------
--   A Data instance
-- --------------------------------------------------------------------}
--
-- -- This instance preserves data abstraction at the cost of inefficiency.
-- -- We omit reflection services for the sake of data abstraction.
--
-- instance (Data k, Data a, GCompare k) => Data (DMap k) where
--   gfoldl f z m   = z fromList `f` toList m
--   toConstr _     = error "toConstr"
--   gunfold _ _    = error "gunfold"
--   dataTypeOf _   = mkNoRepType "Data.Map.Map"
--   dataCast2 f    = gcast2 f
--
-- #endif

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | /O(1)/. A map with a single element.
--
-- > singleton 1 'a'        == fromList [(1, 'a')]
-- > size (singleton 1 'a') == 1
singleton :: k v -> f v -> DMap k f
singleton = singletonE

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(1)/. The number of elements in the map.
size :: DMap k f -> Int
size = sizeE

-- | /O(log n)/. Is the key a member of the map? See also 'notMember'.
member :: GCompare k => k a -> DMap k f -> Bool
member k = isJust . lookup k

-- | /O(log n)/. Is the key not a member of the map? See also 'member'.
notMember :: GCompare k => k v -> DMap k f -> Bool
notMember k m = not (member k m)

-- | /O(log n)/. Lookup the value at a key in the map.
--
-- The function will return the corresponding value as @('Just' value)@,
-- or 'Nothing' if the key isn't in the map.
lookup :: forall k f v. GCompare k => k v -> DMap k f -> Maybe (f v)
lookup = lookupE

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.
-- Consider using 'lookup' when elements may not be present.
find :: GCompare k => k v -> DMap k f -> f v
find k m = case lookup k m of
    Nothing -> error "DMap.find: element not in the map"
    Just v  -> v

-- | /O(log n)/. The expression @('findWithDefault' def k map)@ returns
-- the value at key @k@ or returns default value @def@
-- when the key is not in the map.
findWithDefault :: GCompare k => f v -> k v -> DMap k f -> f v
findWithDefault def k m = case lookup k m of
    Nothing -> def
    Just v  -> v

{--------------------------------------------------------------------
  Insertion
--------------------------------------------------------------------}

-- | /O(log n)/. Insert a new key and value in the map.
-- If the key is already present in the map, the associated value is
-- replaced with the supplied value. 'insert' is equivalent to
-- @'insertWith' 'const'@.
insert :: forall k f v. GCompare k => k v -> f v -> DMap k f -> DMap k f
insert kx x = Bin' . makeInsert kx x

-- | /O(log n)/. Insert a new key and value in the map if the key
-- is not already present. If the key is already present, @insertR@
-- does nothing.
insertR :: forall k f v. GCompare k => k v -> f v -> DMap k f -> DMap k f
insertR kx x = Bin' . makeInsertR kx x

-- | /O(log n)/. Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@
-- will insert the entry @key :=> value@ into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the entry @key :=> f new_value old_value@.
insertWith :: GCompare k => (f v -> f v -> f v) -> k v -> f v -> DMap k f -> DMap k f
insertWith f = insertWithKey (\_ x' y' -> f x' y')

-- | Same as 'insertWith', but the combining function is applied strictly.
-- This is often the most desirable behavior.
insertWith' :: GCompare k => (f v -> f v -> f v) -> k v -> f v -> DMap k f -> DMap k f
insertWith' f = insertWithKey' (\_ x' y' -> f x' y')

-- | /O(log n)/. Insert with a function, combining key, new value and old value.
-- @'insertWithKey' f key value mp@
-- will insert the entry @key :=> value@ into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the entry @key :=> f key new_value old_value@.
-- Note that the key passed to f is the same key passed to 'insertWithKey'.
insertWithKey :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> DMap k f -> DMap k f
insertWithKey f kx x = Bin' . makeInsertWithKey f kx x

-- | Same as 'insertWithKey', but the combining function is applied strictly.
insertWithKey' :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> DMap k f -> DMap k f
insertWithKey' f kx x = Bin' . makeInsertWithKey' f kx x

-- | /O(log n)/. Combines insert operation with old value retrieval.
-- The expression (@'insertLookupWithKey' f k x map@)
-- is a pair where the first element is equal to (@'lookup' k map@)
-- and the second element equal to (@'insertWithKey' f k x map@).
insertLookupWithKey :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> DMap k f
                    -> (Maybe (f v), DMap k f)
insertLookupWithKey f kx x = fmap Bin' . makeInsertLookupWithKey f kx x

-- | /O(log n)/. A strict version of 'insertLookupWithKey'.
insertLookupWithKey' :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> DMap k f
                     -> (Maybe (f v), DMap k f)
insertLookupWithKey' f kx x = fmap Bin' . makeInsertLookupWithKey' f kx x

{--------------------------------------------------------------------
  Deletion
  [delete] is the inlined version of [deleteWith (\k x -> Nothing)]
--------------------------------------------------------------------}

-- | /O(log n)/. Delete a key and its value from the map. When the key is not
-- a member of the map, the original map is returned.
delete :: forall k f v. GCompare k => k v -> DMap k f -> DMap k f
delete k = fst $ makeDelete k

-- | /O(log n)/. Update a value at a specific key with the result of the provided function.
-- When the key is not
-- a member of the map, the original map is returned.
adjust :: GCompare k => (f v -> f v) -> k v -> DMap k f -> DMap k f
adjust f = adjustWithKey (\_ x -> f x)

-- | Works the same as 'adjust' except the new value is return in some 'Applicative' @f@.
adjustF
  :: forall k f v g
  .  (GCompare  k, Applicative f)
  => k v
  -> (g v -> f (g v))
  -> DMap k g -> f (DMap k g)
adjustF k f = fst $ makeAdjustF f k

-- | /O(log n)/. Adjust a value at a specific key. When the key is not
-- a member of the map, the original map is returned.
adjustWithKey :: GCompare k => (k v -> f v -> f v) -> k v -> DMap k f -> DMap k f
adjustWithKey f k = fst $ makeAdjustWithKey f k

-- | /O(log n)/. A strict version of 'adjustWithKey'.
adjustWithKey' :: GCompare k => (k v -> f v -> f v) -> k v -> DMap k f -> DMap k f
adjustWithKey' f k = fst $ makeAdjustWithKey' f k

-- | /O(log n)/. The expression (@'update' f k map@) updates the value @x@
-- at @k@ (if it is in the map). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @k@ is bound to the new value @y@.
update :: GCompare k => (f v -> Maybe (f v)) -> k v -> DMap k f -> DMap k f
update f = updateWithKey (\_ x -> f x)

-- | /O(log n)/. The expression (@'updateWithKey' f k map@) updates the
-- value @x@ at @k@ (if it is in the map). If (@f k x@) is 'Nothing',
-- the element is deleted. If it is (@'Just' y@), the key @k@ is bound
-- to the new value @y@.
updateWithKey :: forall k f v. GCompare k => (k v -> f v -> Maybe (f v)) -> k v -> DMap k f -> DMap k f
updateWithKey f k = fst $ makeUpdateWithKey f k

-- | /O(log n)/. Lookup and update. See also 'updateWithKey'.
-- The function returns changed value, if it is updated.
-- Returns the original key value if the map entry is deleted.
updateLookupWithKey :: forall k f v. GCompare k => (k v -> f v -> Maybe (f v)) -> k v -> DMap k f -> (Maybe (f v), DMap k f)
updateLookupWithKey f k = fst $ makeUpdateLookupWithKey f k

-- | /O(log n)/. The expression (@'alter' f k map@) alters the value @x@ at @k@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in a 'Map'.
-- In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter :: forall k f v. GCompare k => (Maybe (f v) -> Maybe (f v)) -> k v -> DMap k f -> DMap k f
alter k f = fst $ makeAlter k f

-- | Works the same as 'alter' except the new value is return in some 'Functor' @f@.
-- In short : @(\v' -> alter (const v') k dm) <$> f (lookup k dm)@
alterF :: forall k f v g. (GCompare  k, Functor f) => k v -> (Maybe (g v) -> f (Maybe (g v))) -> DMap k g -> f (DMap k g)
alterF k f = fst $ makeAlterF k f

{--------------------------------------------------------------------
  Indexing
--------------------------------------------------------------------}

-- | /O(log n)/. Return the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map. Calls 'error' when
-- the key is not a 'member' of the map.
findIndex :: GCompare k => k v -> DMap k f -> Int
findIndex k t
  = case lookupIndex k t of
      Nothing  -> error "Map.findIndex: element is not in the map"
      Just idx -> idx

-- | /O(log n)/. Lookup the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map.
lookupIndex :: forall k f v. GCompare k => k v -> DMap k f -> Maybe Int
lookupIndex k = fst $ makeLookupIndex k

-- | /O(log n)/. Retrieve an element by /index/. Calls 'error' when an
-- invalid index is used.
elemAt :: Int -> DMap k f -> DSum k f
elemAt = fst makElemAt

-- | /O(log n)/. Update the element at /index/. Does nothing when an
-- invalid index is used.
updateAt :: (forall v. k v -> f v -> Maybe (f v)) -> Int -> DMap k f -> DMap k f
updateAt f i0 = fst $ makeUpdateAt f i0

-- | /O(log n)/. Delete the element at /index/.
-- Defined as (@'deleteAt' i map = 'updateAt' (\k x -> 'Nothing') i map@).
deleteAt :: Int -> DMap k f -> DMap k f
deleteAt i m
  = updateAt (\_ _ -> Nothing) i m


{--------------------------------------------------------------------
  Minimal, Maximal
--------------------------------------------------------------------}

-- | /O(log n)/. The minimal key of the map. Calls 'error' is the map is empty.
findMin :: DMap k f -> DSum k f
findMin m = case lookupMin m of
  Just x -> x
  Nothing -> error "Map.findMin: empty map has no minimal element"

lookupMin :: DMap k f -> Maybe (DSum k f)
lookupMin = fst makeLookupMin

-- | /O(log n)/. The maximal key of the map. Calls 'error' is the map is empty.
findMax :: DMap k f -> DSum k f
findMax m = case lookupMax m of
  Just x -> x
  Nothing -> error "Map.findMax: empty map has no maximal element"

lookupMax :: DMap k f -> Maybe (DSum k f)
lookupMax = fst makeLookupMax

-- | /O(log n)/. Delete the minimal key. Returns an empty map if the map is empty.
deleteMin :: DMap k f -> DMap k f
deleteMin = fst makeDeleteMin

-- | /O(log n)/. Delete the maximal key. Returns an empty map if the map is empty.
deleteMax :: DMap k f -> DMap k f
deleteMax = fst makeDeleteMax

-- | /O(log n)/. Update the value at the minimal key.
updateMinWithKey :: (forall v. k v -> f v -> Maybe (f v)) -> DMap k f -> DMap k f
updateMinWithKey f = fst $ makeUpdateMinWithKey f

-- | /O(log n)/. Update the value at the maximal key.
updateMaxWithKey :: (forall v. k v -> f v -> Maybe (f v)) -> DMap k f -> DMap k f
updateMaxWithKey f = fst $ makeUpdateMaxWithKey f

{--------------------------------------------------------------------
  Union.
--------------------------------------------------------------------}

-- | The union of a list of maps:
--   (@'unions' == 'Prelude.foldl' 'union' 'empty'@).
unions :: GCompare k => [DMap k f] -> DMap k f
unions ts
  = foldlStrict union empty ts

-- | The union of a list of maps, with a combining operation:
--   (@'unionsWithKey' f == 'Prelude.foldl' ('unionWithKey' f) 'empty'@).
unionsWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> [DMap k f] -> DMap k f
unionsWithKey f ts
  = foldlStrict (unionWithKey f) empty ts

-- | /O(m*log(n\/m + 1)), m <= n/.
-- The expression (@'union' t1 t2@) takes the left-biased union of @t1@ and @t2@.
-- It prefers @t1@ when duplicate keys are encountered,
-- i.e. (@'union' == 'unionWith' 'const'@).
union :: GCompare k => DMap k f -> DMap k f -> DMap k f
union t1 t2 = fst makeUnion t1 t2

{--------------------------------------------------------------------
  Union with a combining function
--------------------------------------------------------------------}

-- | /O(n+m)/.
-- Union with a combining function.
unionWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> DMap k f -> DMap k f -> DMap k f
unionWithKey f = fst $ makeUnionWithKey f

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

-- | /O(m * log (n\/m + 1)), m <= n/. Difference of two maps.
-- Return elements of the first map not existing in the second map.
difference :: GCompare k => DMap k f -> DMap k g -> DMap k f
difference = fst makeDifference

-- | /O(n+m)/. Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and both values.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWithKey :: GCompare k => (forall v. k v -> f v -> g v -> Maybe (f v)) -> DMap k f -> DMap k g -> DMap k f
differenceWithKey f = fst $ makeDifferenceWithKey f

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

-- | /O(m * log (n\/m + 1), m <= n/. Intersection of two maps.
-- Return data in the first map for the keys existing in both maps.
-- (@'intersection' m1 m2 == 'intersectionWith' 'const' m1 m2@).
intersection :: GCompare k => DMap k f -> DMap k f -> DMap k f
intersection = fst makeIntersection

-- | /O(m * log (n\/m + 1), m <= n/. Intersection with a combining function.
intersectionWithKey :: GCompare k => (forall v. k v -> f v -> g v -> h v) -> DMap k f -> DMap k g -> DMap k h
intersectionWithKey f = fst $ makeIntersectionWithKey f

{--------------------------------------------------------------------
  Submap
--------------------------------------------------------------------}
-- | /O(n+m)/.
-- This function is defined as (@'isSubmapOf' = 'isSubmapOfBy' 'eqTagged')@).
--
isSubmapOf
  :: forall k f
  .  (GCompare k, Has' Eq k f)
  => DMap k f -> DMap k f -> Bool
isSubmapOf m1 m2 = isSubmapOfBy (\k _ x0 x1 -> has' @Eq @f k (x0 == x1)) m1 m2

{- | /O(n+m)/.
 The expression (@'isSubmapOfBy' f t1 t2@) returns 'True' if
 all keys in @t1@ are in tree @t2@, and when @f@ returns 'True' when
 applied to their respective keys and values.
-}
isSubmapOfBy :: GCompare k => (forall v. k v -> k v -> f v -> g v -> Bool) -> DMap k f -> DMap k g -> Bool
isSubmapOfBy f t1 t2
  = (size t1 <= size t2) && (submap' f t1 t2)

submap' :: GCompare k => (forall v. k v -> k v -> f v -> g v -> Bool) -> DMap k f -> DMap k g -> Bool
submap' f t1 t2 = fst (makeSubmap' f) t1 t2

-- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
-- Defined as (@'isProperSubmapOf' = 'isProperSubmapOfBy' 'eqTagged'@).
isProperSubmapOf
  :: forall k f
  .  (GCompare k, Has' Eq k f)
  => DMap k f -> DMap k f -> Bool
isProperSubmapOf m1 m2
  = isProperSubmapOfBy (\k _ x0 x1 -> has' @Eq @f k (x0 == x1)) m1 m2

{- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
 The expression (@'isProperSubmapOfBy' f m1 m2@) returns 'True' when
 @m1@ and @m2@ are not equal,
 all keys in @m1@ are in @m2@, and when @f@ returns 'True' when
 applied to their respective keys and values.
-}
isProperSubmapOfBy :: GCompare k => (forall v. k v -> k v -> f v -> g v -> Bool) -> DMap k f -> DMap k g -> Bool
isProperSubmapOfBy f t1 t2
  = (size t1 < size t2) && (submap' f t1 t2)

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}

-- | /O(n)/. Filter all keys\/values that satisfy the predicate.
filterWithKey :: GCompare k => (forall v. k v -> f v -> Bool) -> DMap k f -> DMap k f
filterWithKey = makeFilterWithKey

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
partitionWithKey :: GCompare k => (forall v. k v -> f v -> Bool) -> DMap k f -> (DMap k f, DMap k f)
partitionWithKey = makePartitionWithKey

-- | /O(n)/. Map values and collect the 'Just' results.
mapMaybe :: GCompare k => (forall v. f v -> Maybe (g v)) -> DMap k f -> DMap k g
mapMaybe f = mapMaybeWithKey (const f)

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
mapMaybeWithKey :: GCompare k => (forall v. k v -> f v -> Maybe (g v)) -> DMap k f -> DMap k g
mapMaybeWithKey = makeMapMaybeWithKey

-- | /O(n)/. Map keys\/values and separate the 'Left' and 'Right' results.
mapEitherWithKey :: GCompare k =>
  (forall v. k v -> f v -> Either (g v) (h v)) -> DMap k f -> (DMap k g, DMap k h)
mapEitherWithKey = makeMapEitherWithKey

{--------------------------------------------------------------------
  Mapping
--------------------------------------------------------------------}

-- | /O(n)/. Map a function over all values in the map.
map :: (forall v. f v -> g v) -> DMap k f -> DMap k g
map f = fst $ makeMap f

-- | /O(n)/. Map a function over all values in the map.
mapWithKey :: (forall v. k v -> f v -> g v) -> DMap k f -> DMap k g
mapWithKey f = fst $ makeMapWithKey f

-- | /O(n)/.
-- @'traverseWithKey' f m == 'fromList' <$> 'traverse' (\(k, v) -> (,) k <$> f k v) ('toList' m)@
-- That is, behaves exactly like a regular 'traverse' except that the traversing
-- function also has access to the key associated with a value.
traverseWithKey :: Applicative t => (forall v. k v -> f v -> t (g v)) -> DMap k f -> t (DMap k g)
traverseWithKey f = fst $ makeTraverseWithKey f

-- | /O(n)/. The function 'mapAccumLWithKey' threads an accumulating
-- argument throught the map in ascending order of keys.
mapAccumLWithKey :: (forall v. a -> k v -> f v -> (a, g v)) -> a -> DMap k f -> (a, DMap k g)
mapAccumLWithKey f = fst $ makeMapAccumLWithKey f

-- | /O(n)/. The function 'mapAccumRWithKey' threads an accumulating
-- argument through the map in descending order of keys.
mapAccumRWithKey :: (forall v. a -> k v -> f v -> (a, g v)) -> a -> DMap k f -> (a, DMap k g)
mapAccumRWithKey f = fst $ makeMapAccumRWithKey f

-- | /O(n*log n)/.
-- @'mapKeysWith' c f s@ is the map obtained by applying @f@ to each key of @s@.
--
-- The size of the result may be smaller if @f@ maps two or more distinct
-- keys to the same new key.  In this case the associated values will be
-- combined using @c@.
mapKeysWith :: GCompare k2 => (forall v. k2 v -> f v -> f v -> f v) -> (forall v. k1 v -> k2 v) -> DMap k1 f -> DMap k2 f
mapKeysWith c f = fromListWithKey c . Prelude.map fFirst . toList
    where fFirst (x :=> y) = (f x :=> y)


-- | /O(n)/.
-- @'mapKeysMonotonic' f s == 'mapKeys' f s@, but works only when @f@
-- is strictly monotonic.
-- That is, for any values @x@ and @y@, if @x@ < @y@ then @f x@ < @f y@.
-- /The precondition is not checked./
-- Semi-formally, we have:
--
-- > and [x < y ==> f x < f y | x <- ls, y <- ls]
-- >                     ==> mapKeysMonotonic f s == mapKeys f s
-- >     where ls = keys s
--
-- This means that @f@ maps distinct original keys to distinct resulting keys.
-- This function has better performance than 'mapKeys'.
mapKeysMonotonic :: (forall v. k1 v -> k2 v) -> DMap k1 f -> DMap k2 f
mapKeysMonotonic f = fst $ makeMapKeysMonotonic f

{--------------------------------------------------------------------
  Folds
--------------------------------------------------------------------}

-- | /O(n)/. Fold the keys and values in the map, such that
-- @'foldWithKey' f z == 'Prelude.foldr' ('uncurry' f) z . 'toAscList'@.
--
-- This is identical to 'foldrWithKey', and you should use that one instead of
-- this one.  This name is kept for backward compatibility.
foldWithKey :: (forall v. k v -> f v -> b -> b) -> b -> DMap k f -> b
foldWithKey = foldrWithKey
{-# DEPRECATED foldWithKey "Use foldrWithKey instead" #-}

-- | /O(n)/. Post-order fold.  The function will be applied from the lowest
-- value to the highest.
foldrWithKey :: (forall v. k v -> f v -> b -> b) -> b -> DMap k f -> b
foldrWithKey = makeFoldrWithKey

-- | /O(n)/. Pre-order fold.  The function will be applied from the highest
-- value to the lowest.
foldlWithKey :: (forall v. b -> k v -> f v -> b) -> b -> DMap k f -> b
foldlWithKey = makeFoldlWithKey

{-
-- | /O(n)/. A strict version of 'foldlWithKey'.
foldlWithKey' :: (b -> k -> a -> b) -> b -> DMap k -> b
foldlWithKey' f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = z `seq` go (f (go z l) kx x) r
-}

{--------------------------------------------------------------------
  List variations
--------------------------------------------------------------------}

-- | /O(n)/. Return all keys of the map in ascending order.
--
-- > keys (fromList [(5,"a"), (3,"b")]) == [3,5]
-- > keys empty == []

keys  :: DMap k f -> [Some k]
keys m
  = [This k | (k :=> _) <- assocs m]

-- | /O(n)/. Return all key\/value pairs in the map in ascending key order.
assocs :: DMap k f -> [DSum k f]
assocs m
  = toList m

{--------------------------------------------------------------------
  Lists
  use [foldlStrict] to reduce demand on the control-stack
--------------------------------------------------------------------}

-- | /O(n*log n)/. Build a map from a list of key\/value pairs. See also 'fromAscList'.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
fromList :: GCompare k => [DSum k f] -> DMap k f
fromList xs
  = foldlStrict ins empty xs
  where
    ins :: GCompare k => DMap k f -> DSum k f -> DMap k f
    ins t (k :=> x) = insert k x t

-- | /O(n*log n)/. Build a map from a list of key\/value pairs with a combining function. See also 'fromAscListWithKey'.
fromListWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> [DSum k f] -> DMap k f
fromListWithKey f xs
  = foldlStrict (ins f) empty xs
  where
    ins :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> DMap k f -> DSum k f -> DMap k f
    ins f t (k :=> x) = insertWithKey f k x t

-- | /O(n)/. Convert to a list of key\/value pairs.
toList :: DMap k f -> [DSum k f]
toList t      = toAscList t

-- | /O(n)/. Convert to an ascending list.
toAscList :: DMap k f -> [DSum k f]
toAscList t   = foldrWithKey (\k x xs -> (k :=> x):xs) [] t

-- | /O(n)/. Convert to a descending list.
toDescList :: DMap k f -> [DSum k f]
toDescList t  = foldlWithKey (\xs k x -> (k :=> x):xs) [] t

{--------------------------------------------------------------------
  Building trees from ascending/descending lists can be done in linear time.

  Note that if [xs] is ascending that:
    fromAscList xs       == fromList xs
    fromAscListWith f xs == fromListWith f xs
--------------------------------------------------------------------}

-- | /O(n)/. Build a map from an ascending list in linear time.
-- /The precondition (input list is ascending) is not checked./
fromAscList :: GEq k => [DSum k f] -> DMap k f
fromAscList xs
  = fromAscListWithKey (\_ x _ -> x) xs

-- | /O(n)/. Build a map from an ascending list in linear time with a
-- combining function for equal keys.
-- /The precondition (input list is ascending) is not checked./
fromAscListWithKey :: GEq k => (forall v. k v -> f v -> f v -> f v) -> [DSum k f] -> DMap k f
fromAscListWithKey f xs
  = fromDistinctAscList (combineEq f xs)
  where
  -- [combineEq f xs] combines equal elements with function [f] in an ordered list [xs]
  combineEq _ xs'
    = case xs' of
        []     -> []
        [x]    -> [x]
        (x:xx) -> combineEq' f x xx

  combineEq' :: GEq k => (forall v. k v -> f v -> f v -> f v) -> DSum k f -> [DSum k f] -> [DSum k f]
  combineEq' f z [] = [z]
  combineEq' f z@(kz :=> zz) (x@(kx :=> xx):xs') =
    case geq kx kz of
        Just Refl   -> let yy = f kx xx zz in combineEq' f (kx :=> yy) xs'
        Nothing     -> z : combineEq' f x xs'


-- | /O(n)/. Build a map from an ascending list of distinct elements in linear time.
-- /The precondition is not checked./
fromDistinctAscList :: [DSum k f] -> DMap k f
fromDistinctAscList = fst makeFromDistinctAscList

{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}

-- | /O(log n)/. The expression (@'split' k map@) is a pair @(map1,map2)@ where
-- the keys in @map1@ are smaller than @k@ and the keys in @map2@ larger than @k@.
-- Any key equal to @k@ is found in neither @map1@ nor @map2@.
split :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, DMap k f)
split = fst . makeSplit
{-# INLINABLE split #-}

-- | /O(log n)/. The expression (@'splitLookup' k map@) splits a map just
-- like 'split' but also returns @'lookup' k map@.
splitLookup :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, Maybe (f v), DMap k f)
splitLookup = fst . makeSplitLookup

-- | /O(log n)/. The expression (@'splitMember' k map@) splits a map just
-- like 'split' but also returns @'member' k map@.
splitMember :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, Bool, DMap k f)
splitMember = fst . makeSplitMember

-- | /O(log n)/.
splitLookupWithKey :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, Maybe (k v, f v), DMap k f)
splitLookupWithKey = fst . makeSplitLookupWithKey

{--------------------------------------------------------------------
  Eq converts the tree to a list. In a lazy setting, this
  actually seems one of the faster methods to compare two trees
  and it is certainly the simplest :-)
--------------------------------------------------------------------}
instance (GEq k, Has' Eq k f) => Eq (DMap k f) where
  t1 == t2  = (size t1 == size t2) && (toAscList t1 == toAscList t2)

{--------------------------------------------------------------------
  Ord
--------------------------------------------------------------------}

instance (GCompare k, Has' Eq k f, Has' Ord k f) => Ord (DMap k f) where
  compare m1 m2 = compare (toAscList m1) (toAscList m2)

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}

instance (GCompare k, GRead k, Has' Read k f) => Read (DMap k f) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    return (fromList xs)

  readListPrec = readListPrecDefault

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
instance (GShow k, Has' Show k f) => Show (DMap k f) where
    showsPrec p m = showParen (p>10)
        ( showString "fromList "
        . showsPrec 11 (toList m)
        )

-- | /O(n)/. Show the tree that implements the map. The tree is shown
-- in a compressed, hanging format. See 'showTreeWith'.
showTree :: (GShow k, Has' Show k f) => DMap k f -> String
showTree m
  = showTreeWith showElem True False m
  where
    showElem :: (GShow k, Has' Show k f) => k v -> f v -> String
    showElem k x  = show (k :=> x)


{- | /O(n)/. The expression (@'showTreeWith' showelem hang wide map@) shows
 the tree that implements the map. Elements are shown using the @showElem@ function. If @hang@ is
 'True', a /hanging/ tree is shown otherwise a rotated tree is shown. If
 @wide@ is 'True', an extra wide version is shown.
-}
showTreeWith :: (forall v. k v -> f v -> String) -> Bool -> Bool -> DMap k f -> String
showTreeWith showelem hang wide t
  | hang      = (showsTreeHang showelem wide [] t) ""
  | otherwise = (showsTree showelem wide [] [] t) ""

showsTree :: (forall v. k v -> f v -> String) -> Bool -> [String] -> [String] -> DMap k f -> ShowS
showsTree showelem wide = fst $ makeShowsTree showelem wide

showsTreeHang :: (forall v. k v -> f v -> String) -> Bool -> [String] -> DMap k f -> ShowS
showsTreeHang showelem wide = fst $ makeShowsTreeHang showelem wide

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}

-- | /O(n)/. Test if the internal map structure is valid.
valid :: GCompare k => DMap k f -> Bool
valid t
  = balanced t && ordered t && validsize t

ordered :: GCompare k => DMap k f -> Bool
ordered = fst makeOrdered

-- | Exported only for "Debug.QuickCheck"
balanced :: DMap k f -> Bool
balanced = fst makeBalanced

validsize :: DMap k f -> Bool
validsize = fst makeValidsize
