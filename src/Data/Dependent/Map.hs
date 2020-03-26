{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Dependent.Map
    ( DMap

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
    , ffor
    , mapWithKey
    , fforWithKey
    , traverseWithKey_
    , forWithKey_
    , traverseWithKey
    , forWithKey
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
import Data.Constraint.Extras (Has', has')
import Data.Dependent.Sum (DSum((:=>)))
import Data.GADT.Compare (GCompare, GEq, GOrdering(..), gcompare, geq)
import Data.GADT.Show (GRead, GShow)
import Data.Maybe (isJust)
import Data.Some (Some, mkSome)
import Data.Typeable ((:~:)(Refl))
import Text.Read (Lexeme(Ident), lexP, parens, prec, readListPrec,
                  readListPrecDefault, readPrec)

#if !MIN_VERSION_base(4,11,0)
import Data.Semigroup (Semigroup, (<>))
#endif

import Data.Dependent.Map.Internal
import Data.Dependent.Map.PtrEquality (ptrEq)

instance (GCompare k) => Monoid (DMap k f) where
    mempty  = empty
    mappend = union
    mconcat = unions

instance (GCompare k) => Semigroup (DMap k f) where
  (<>) = mappend

{--------------------------------------------------------------------
  Operators
--------------------------------------------------------------------}
infixl 9 \\,! -- \\ at the end of the line means line continuation

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
  Query
--------------------------------------------------------------------}

-- | /O(log n)/. Is the key a member of the map? See also 'notMember'.
member :: GCompare k => k a -> DMap k f -> Bool
member k = isJust . lookup k

-- | /O(log n)/. Is the key not a member of the map? See also 'member'.
notMember :: GCompare k => k v -> DMap k f -> Bool
notMember k m = not (member k m)

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
insert kx x = kx `seq` go
    where
        go :: DMap k f -> DMap k f
        go Tip = singleton kx x
        go t@(Bin sz ky y l r) = case gcompare kx ky of
            GLT -> let !l' = go l
                   in if l' `ptrEq` l
                      then t
                      else balance ky y l' r
            GGT -> let !r' = go r
                   in if r' `ptrEq` r
                      then t
                      else balance ky y l r'
            GEQ
              | kx `ptrEq` ky && x `ptrEq` y -> t
              | otherwise -> Bin sz kx x l r

-- | /O(log n)/. Insert a new key and value in the map if the key
-- is not already present. If the key is already present, @insertR@
-- does nothing.
insertR :: forall k f v. GCompare k => k v -> f v -> DMap k f -> DMap k f
insertR kx x = kx `seq` go
    where
        go :: DMap k f -> DMap k f
        go Tip = singleton kx x
        go t@(Bin sz ky y l r) = case gcompare kx ky of
            GLT -> let !l' = go l
                   in if l' `ptrEq` l
                      then t
                      else balance ky y l' r
            GGT -> let !r' = go r
                   in if r' `ptrEq` r
                   then t
                   else balance ky y l r'
            GEQ -> t

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
insertWithKey f kx x = kx `seq` go
  where
    go :: DMap k f -> DMap k f
    go Tip = singleton kx x
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> balance ky y (go l) r
            GGT -> balance ky y l (go r)
            GEQ -> Bin sy kx (f kx x y) l r

-- | Same as 'insertWithKey', but the combining function is applied strictly.
insertWithKey' :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> DMap k f -> DMap k f
insertWithKey' f kx x = kx `seq` go
  where
    go :: DMap k f -> DMap k f
    go Tip = singleton kx $! x
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> balance ky y (go l) r
            GGT -> balance ky y l (go r)
            GEQ -> let x' = f kx x y in seq x' (Bin sy kx x' l r)

-- | /O(log n)/. Combines insert operation with old value retrieval.
-- The expression (@'insertLookupWithKey' f k x map@)
-- is a pair where the first element is equal to (@'lookup' k map@)
-- and the second element equal to (@'insertWithKey' f k x map@).
insertLookupWithKey :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> DMap k f
                    -> (Maybe (f v), DMap k f)
insertLookupWithKey f kx x = kx `seq` go
  where
    go :: DMap k f -> (Maybe (f v), DMap k f)
    go Tip = (Nothing, singleton kx x)
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> let (found, l') = go l
                  in (found, balance ky y l' r)
            GGT -> let (found, r') = go r
                  in (found, balance ky y l r')
            GEQ -> (Just y, Bin sy kx (f kx x y) l r)

-- | /O(log n)/. A strict version of 'insertLookupWithKey'.
insertLookupWithKey' :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> DMap k f
                     -> (Maybe (f v), DMap k f)
insertLookupWithKey' f kx x = kx `seq` go
  where
    go :: DMap k f -> (Maybe (f v), DMap k f)
    go Tip = x `seq` (Nothing, singleton kx x)
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> let (found, l') = go l
                  in (found, balance ky y l' r)
            GGT -> let (found, r') = go r
                  in (found, balance ky y l r')
            GEQ -> let x' = f kx x y in x' `seq` (Just y, Bin sy kx x' l r)

{--------------------------------------------------------------------
  Deletion
  [delete] is the inlined version of [deleteWith (\k x -> Nothing)]
--------------------------------------------------------------------}

-- | /O(log n)/. Delete a key and its value from the map. When the key is not
-- a member of the map, the original map is returned.
delete :: forall k f v. GCompare k => k v -> DMap k f -> DMap k f
delete k = k `seq` go
  where
    go :: DMap k f -> DMap k f
    go Tip = Tip
    go (Bin _ kx x l r) =
        case gcompare k kx of
            GLT -> balance kx x (go l) r
            GGT -> balance kx x l (go r)
            GEQ -> glue l r

-- | /O(log n)/. Update a value at a specific key with the result of the provided function.
-- When the key is not
-- a member of the map, the original map is returned.
adjust :: GCompare k => (f v -> f v) -> k v -> DMap k f -> DMap k f
adjust f = adjustWithKey (\_ x -> f x)

-- | /O(log n)/. Adjust a value at a specific key. When the key is not
-- a member of the map, the original map is returned.
adjustWithKey :: GCompare k => (k v -> f v -> f v) -> k v -> DMap k f -> DMap k f
adjustWithKey f0 !k0 = go f0 k0
  where
    go :: GCompare k => (k v -> f v -> f v) -> k v -> DMap k f -> DMap k f
    go _f _k Tip = Tip
    go f k (Bin sx kx x l r) =
      case gcompare k kx of
        GLT -> Bin sx kx x (go f k l) r
        GGT -> Bin sx kx x l (go f k r)
        GEQ -> Bin sx kx (f kx x) l r

-- | /O(log n)/. A strict version of 'adjustWithKey'.
adjustWithKey' :: GCompare k => (k v -> f v -> f v) -> k v -> DMap k f -> DMap k f
adjustWithKey' f0 !k0 = go f0 k0
  where
    go :: GCompare k => (k v -> f v -> f v) -> k v -> DMap k f -> DMap k f
    go _f _k Tip = Tip
    go f k (Bin sx kx x l r) =
      case gcompare k kx of
        GLT -> Bin sx kx x (go f k l) r
        GGT -> Bin sx kx x l (go f k r)
        GEQ -> let !x' = f kx x in Bin sx kx x' l r

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
updateWithKey f k = k `seq` go
  where
    go :: DMap k f -> DMap k f
    go Tip = Tip
    go (Bin sx kx x l r) =
        case gcompare k kx of
           GLT -> balance kx x (go l) r
           GGT -> balance kx x l (go r)
           GEQ -> case f kx x of
                   Just x' -> Bin sx kx x' l r
                   Nothing -> glue l r

-- | /O(log n)/. Lookup and update. See also 'updateWithKey'.
-- The function returns changed value, if it is updated.
-- Returns the original key value if the map entry is deleted.
updateLookupWithKey :: forall k f v. GCompare k => (k v -> f v -> Maybe (f v)) -> k v -> DMap k f -> (Maybe (f v), DMap k f)
updateLookupWithKey f k = k `seq` go
 where
   go :: DMap k f -> (Maybe (f v), DMap k f)
   go Tip = (Nothing,Tip)
   go (Bin sx kx x l r) =
          case gcompare k kx of
               GLT -> let (found,l') = go l in (found,balance kx x l' r)
               GGT -> let (found,r') = go r in (found,balance kx x l r')
               GEQ -> case f kx x of
                       Just x' -> (Just x',Bin sx kx x' l r)
                       Nothing -> (Just x,glue l r)

-- | /O(log n)/. The expression (@'alter' f k map@) alters the value @x@ at @k@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in a 'Map'.
-- In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter :: forall k f v. GCompare k => (Maybe (f v) -> Maybe (f v)) -> k v -> DMap k f -> DMap k f
alter f k = k `seq` go
  where
    go :: DMap k f -> DMap k f
    go Tip = case f Nothing of
               Nothing -> Tip
               Just x  -> singleton k x

    go (Bin sx kx x l r) = case gcompare k kx of
               GLT -> balance kx x (go l) r
               GGT -> balance kx x l (go r)
               GEQ -> case f (Just x) of
                       Just x' -> Bin sx kx x' l r
                       Nothing -> glue l r

-- | Works the same as 'alter' except the new value is returned in some 'Functor' @f@.
-- In short : @(\v' -> alter (const v') k dm) <$> f (lookup k dm)@
alterF :: forall k f v g. (GCompare  k, Functor f) => k v -> (Maybe (g v) -> f (Maybe (g v))) -> DMap k g -> f (DMap k g)
alterF k f = go
  where
    go :: DMap k g -> f (DMap k g)
    go Tip = maybe Tip (singleton k) <$> f Nothing

    go (Bin sx kx x l r) = case gcompare k kx of
      GLT -> (\l' -> balance kx x l' r) <$> go l
      GGT -> (\r' -> balance kx x l r') <$> go r
      GEQ -> maybe (glue l r) (\x' -> Bin sx kx x' l r) <$> f (Just x)

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
lookupIndex k = k `seq` go 0
  where
    go :: Int -> DMap k f -> Maybe Int
    go !idx Tip  = idx `seq` Nothing
    go !idx (Bin _ kx _ l r)
      = case gcompare k kx of
          GLT -> go idx l
          GGT -> go (idx + size l + 1) r
          GEQ -> Just (idx + size l)

-- | /O(log n)/. Retrieve an element by /index/. Calls 'error' when an
-- invalid index is used.
elemAt :: Int -> DMap k f -> DSum k f
elemAt _ Tip = error "Map.elemAt: index out of range"
elemAt i (Bin _ kx x l r)
  = case compare i sizeL of
      LT -> elemAt i l
      GT -> elemAt (i-sizeL-1) r
      EQ -> kx :=> x
  where
    sizeL = size l

-- | /O(log n)/. Update the element at /index/. Does nothing when an
-- invalid index is used.
updateAt :: (forall v. k v -> f v -> Maybe (f v)) -> Int -> DMap k f -> DMap k f
updateAt f i0 t = i0 `seq` go i0 t
 where
    go _ Tip  = Tip
    go i (Bin sx kx x l r) = case compare i sizeL of
      LT -> balance kx x (go i l) r
      GT -> balance kx x l (go (i-sizeL-1) r)
      EQ -> case f kx x of
              Just x' -> Bin sx kx x' l r
              Nothing -> glue l r
      where
        sizeL = size l

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
lookupMin m = case m of
      Tip -> Nothing
      Bin _ kx x l _ -> Just $! go kx x l
  where
    go :: k v -> f v -> DMap k f -> DSum k f
    go kx x Tip = kx :=> x
    go _  _ (Bin _ kx x l _) = go kx x l

-- | /O(log n)/. The maximal key of the map. Calls 'error' is the map is empty.
findMax :: DMap k f -> DSum k f
findMax m = case lookupMax m of
  Just x -> x
  Nothing -> error "Map.findMax: empty map has no maximal element"

lookupMax :: DMap k f -> Maybe (DSum k f)
lookupMax m = case m of
      Tip -> Nothing
      Bin _ kx x _ r -> Just $! go kx x r
  where
    go :: k v -> f v -> DMap k f -> DSum k f
    go kx x Tip = kx :=> x
    go _  _ (Bin _ kx x _ r) = go kx x r

-- | /O(log n)/. Delete the minimal key. Returns an empty map if the map is empty.
deleteMin :: DMap k f -> DMap k f
deleteMin (Bin _ _  _ Tip r)  = r
deleteMin (Bin _ kx x l r)    = balance kx x (deleteMin l) r
deleteMin Tip                 = Tip

-- | /O(log n)/. Delete the maximal key. Returns an empty map if the map is empty.
deleteMax :: DMap k f -> DMap k f
deleteMax (Bin _ _  _ l Tip)  = l
deleteMax (Bin _ kx x l r)    = balance kx x l (deleteMax r)
deleteMax Tip                 = Tip

-- | /O(log n)/. Update the value at the minimal key.
updateMinWithKey :: (forall v. k v -> f v -> Maybe (f v)) -> DMap k f -> DMap k f
updateMinWithKey f = go
 where
    go (Bin sx kx x Tip r) = case f kx x of
                                  Nothing -> r
                                  Just x' -> Bin sx kx x' Tip r
    go (Bin _ kx x l r)    = balance kx x (go l) r
    go Tip                 = Tip

-- | /O(log n)/. Update the value at the maximal key.
updateMaxWithKey :: (forall v. k v -> f v -> Maybe (f v)) -> DMap k f -> DMap k f
updateMaxWithKey f = go
 where
    go (Bin sx kx x l Tip) = case f kx x of
                              Nothing -> l
                              Just x' -> Bin sx kx x' l Tip
    go (Bin _ kx x l r)    = balance kx x l (go r)
    go Tip                 = Tip

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
union t1 Tip  = t1
union t1 (Bin _ kx x Tip Tip) = insertR kx x t1
union Tip t2  = t2
union (Bin _ kx x Tip Tip) t2 = insert kx x t2
union t1@(Bin _ k1 x1 l1 r1) t2 = case split k1 t2 of
  (l2, r2)
    | l1 `ptrEq` l1l2 && r1 `ptrEq` r1r2 -> t1
    | otherwise -> combine k1 x1 l1l2 r1r2
    where !l1l2 = l1 `union` l2
          !r1r2 = r1 `union` r2

{--------------------------------------------------------------------
  Union with a combining function
--------------------------------------------------------------------}

-- | /O(n+m)/.
-- Union with a combining function.
unionWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> DMap k f -> DMap k f -> DMap k f
unionWithKey _ t1 Tip  = t1
unionWithKey _ Tip t2  = t2
unionWithKey f (Bin _ k1 x1 l1 r1) t2 = case splitLookup k1 t2 of
  (l2, mx2, r2) -> case mx2 of
      Nothing -> combine k1 x1 l1l2 r1r2
      Just x2 -> combine k1 (f k1 x1 x2) l1l2 r1r2
    where !l1l2 = unionWithKey f l1 l2
          !r1r2 = unionWithKey f r1 r2

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

-- | /O(m * log (n\/m + 1)), m <= n/. Difference of two maps.
-- Return elements of the first map not existing in the second map.
difference :: GCompare k => DMap k f -> DMap k g -> DMap k f
difference Tip _   = Tip
difference t1 Tip  = t1
difference t1 (Bin _ k2 _x2 l2 r2) = case split k2 t1 of
  (l1, r1)
    | size t1 == size l1l2 + size r1r2 -> t1
    | otherwise -> merge l1l2 r1r2
    where
      !l1l2 = l1 `difference` l2
      !r1r2 = r1 `difference` r2

-- | /O(n+m)/. Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and both values.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWithKey :: GCompare k => (forall v. k v -> f v -> g v -> Maybe (f v)) -> DMap k f -> DMap k g -> DMap k f
differenceWithKey _ Tip _   = Tip
differenceWithKey _ t1 Tip  = t1
differenceWithKey f (Bin _ k1 x1 l1 r1) t2 = case splitLookup k1 t2 of
  (l2, mx2, r2) -> case mx2 of
      Nothing -> combine k1 x1 l1l2 r1r2
      Just x2 -> case f k1 x1 x2 of
        Nothing -> merge l1l2 r1r2
        Just x1x2 -> combine k1 x1x2 l1l2 r1r2
    where !l1l2 = differenceWithKey f l1 l2
          !r1r2 = differenceWithKey f r1 r2

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

-- | /O(m * log (n\/m + 1), m <= n/. Intersection of two maps.
-- Return data in the first map for the keys existing in both maps.
-- (@'intersection' m1 m2 == 'intersectionWith' 'const' m1 m2@).
intersection :: GCompare k => DMap k f -> DMap k f -> DMap k f
intersection Tip _ = Tip
intersection _ Tip = Tip
intersection t1@(Bin s1 k1 x1 l1 r1) t2 =
  let !(l2, found, r2) = splitMember k1 t2
      !l1l2 = intersection l1 l2
      !r1r2 = intersection r1 r2
  in if found
     then if l1l2 `ptrEq` l1 && r1r2 `ptrEq` r1
          then t1
          else combine k1 x1 l1l2 r1r2
     else merge l1l2 r1r2

-- | /O(m * log (n\/m + 1), m <= n/. Intersection with a combining function.
intersectionWithKey :: GCompare k => (forall v. k v -> f v -> g v -> h v) -> DMap k f -> DMap k g -> DMap k h
intersectionWithKey _ Tip _ = Tip
intersectionWithKey _ _ Tip = Tip
intersectionWithKey f (Bin s1 k1 x1 l1 r1) t2 =
  let !(l2, found, r2) = splitLookup k1 t2
      !l1l2 = intersectionWithKey f l1 l2
      !r1r2 = intersectionWithKey f r1 r2
  in case found of
       Nothing -> merge l1l2 r1r2
       Just x2 -> combine k1 (f k1 x1 x2) l1l2 r1r2

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
submap' _ Tip _ = True
submap' _ _ Tip = False
submap' f (Bin _ kx x l r) t
  = case found of
      Nothing -> False
      Just (ky, y)  -> f kx ky x y && submap' f l lt && submap' f r gt
  where
    (lt,found,gt) = splitLookupWithKey kx t

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
filterWithKey p = go
  where
    go Tip = Tip
    go t@(Bin _ kx x l r)
      | p kx x    = if l' `ptrEq` l && r' `ptrEq` r
                    then t
                    else combine kx x l' r'
      | otherwise = merge l' r'
      where !l' = go l
            !r' = go r

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
partitionWithKey :: GCompare k => (forall v. k v -> f v -> Bool) -> DMap k f -> (DMap k f, DMap k f)
partitionWithKey p0 m0 = toPair (go p0 m0)
  where
    go :: GCompare k => (forall v. k v -> f v -> Bool) -> DMap k f -> (DMap k f :*: DMap k f)
    go _ Tip = (Tip :*: Tip)
    go p (Bin _ kx x l r)
      | p kx x    = (combine kx x l1 r1 :*: merge l2 r2)
      | otherwise = (merge l1 r1 :*: combine kx x l2 r2)
      where
        (l1 :*: l2) = go p l
        (r1 :*: r2) = go p r

-- | /O(n)/. Map values and collect the 'Just' results.
mapMaybe :: GCompare k => (forall v. f v -> Maybe (g v)) -> DMap k f -> DMap k g
mapMaybe f = mapMaybeWithKey (const f)

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
mapMaybeWithKey :: GCompare k => (forall v. k v -> f v -> Maybe (g v)) -> DMap k f -> DMap k g
mapMaybeWithKey f = go
  where
    go Tip = Tip
    go (Bin _ kx x l r) = case f kx x of
        Just y  -> combine kx y (go l) (go r)
        Nothing -> merge (go l) (go r)

-- | /O(n)/. Map keys\/values and separate the 'Left' and 'Right' results.
mapEitherWithKey :: GCompare k =>
  (forall v. k v -> f v -> Either (g v) (h v)) -> DMap k f -> (DMap k g, DMap k h)
mapEitherWithKey f0 = toPair . go f0
  where
    go :: GCompare k
       => (forall v. k v -> f v -> Either (g v) (h v))
       -> DMap k f -> (DMap k g :*: DMap k h)
    go _ Tip = (Tip :*: Tip)
    go f (Bin _ kx x l r) = case f kx x of
      Left y  -> (combine kx y l1 r1 :*: merge l2 r2)
      Right z -> (merge l1 r1 :*: combine kx z l2 r2)
      where
        (l1,l2) = mapEitherWithKey f l
        (r1,r2) = mapEitherWithKey f r

{--------------------------------------------------------------------
  Mapping
--------------------------------------------------------------------}

-- | /O(n)/. Map a function over all values in the map.
map :: (forall v. f v -> g v) -> DMap k f -> DMap k g
map f = go
  where
    go Tip = Tip
    go (Bin sx kx x l r) = Bin sx kx (f x) (go l) (go r)

-- | /O(n)/.
-- @'ffor' == 'flip' 'map'@ except we cannot actually use
-- 'flip' because of the lack of impredicative types.
ffor :: DMap k f -> (forall v. f v -> g v) -> DMap k g
ffor m f = map f m

-- | /O(n)/. Map a function over all values in the map.
mapWithKey :: (forall v. k v -> f v -> g v) -> DMap k f -> DMap k g
mapWithKey f = go
  where
    go Tip = Tip
    go (Bin sx kx x l r) = Bin sx kx (f kx x) (go l) (go r)

-- | /O(n)/.
-- @'fforWithKey' == 'flip' 'mapWithKey'@ except we cannot actually use
-- 'flip' because of the lack of impredicative types.
fforWithKey :: DMap k f -> (forall v. k v -> f v -> g v) -> DMap k g
fforWithKey m f = mapWithKey f m

-- | /O(n)/.
-- @'traverseWithKey' f m == 'fromList' <$> 'traverse' (\(k, v) -> (,) k <$> f k v) ('toList' m)@
-- That is, behaves exactly like a regular 'traverse' except that the traversing
-- function also has access to the key associated with a value.
traverseWithKey_ :: Applicative t => (forall v. k v -> f v -> t ()) -> DMap k f -> t ()
traverseWithKey_ f = go
  where
    go Tip = pure ()
    go (Bin 1 k v _ _) = f k v
    go (Bin s k v l r) = go l *> f k v *> go r

-- | /O(n)/.
-- @'forWithKey' == 'flip' 'traverseWithKey'@ except we cannot actually use
-- 'flip' because of the lack of impredicative types.
forWithKey_ :: Applicative t => DMap k f -> (forall v. k v -> f v -> t ()) -> t ()
forWithKey_ m f = traverseWithKey_ f m

-- | /O(n)/.
-- @'traverseWithKey' f m == 'fromList' <$> 'traverse' (\(k, v) -> (,) k <$> f k v) ('toList' m)@
-- That is, behaves exactly like a regular 'traverse' except that the traversing
-- function also has access to the key associated with a value.
traverseWithKey :: Applicative t => (forall v. k v -> f v -> t (g v)) -> DMap k f -> t (DMap k g)
traverseWithKey f = go
  where
    go Tip = pure Tip
    go (Bin 1 k v _ _) = (\v' -> Bin 1 k v' Tip Tip) <$> f k v
    go (Bin s k v l r) = flip (Bin s k) <$> go l <*> f k v <*> go r

-- | /O(n)/.
-- @'forWithKey' == 'flip' 'traverseWithKey'@ except we cannot actually use
-- 'flip' because of the lack of impredicative types.
forWithKey :: Applicative t => DMap k f -> (forall v. k v -> f v -> t (g v)) -> t (DMap k g)
forWithKey m f = traverseWithKey f m

-- | /O(n)/. The function 'mapAccumLWithKey' threads an accumulating
-- argument through the map in ascending order of keys.
mapAccumLWithKey :: (forall v. a -> k v -> f v -> (a, g v)) -> a -> DMap k f -> (a, DMap k g)
mapAccumLWithKey f = go
  where
    go a Tip               = (a,Tip)
    go a (Bin sx kx x l r) =
                 let (a1,l') = go a l
                     (a2,x') = f a1 kx x
                     (a3,r') = go a2 r
                 in (a3,Bin sx kx x' l' r')

-- | /O(n)/. The function 'mapAccumRWithKey' threads an accumulating
-- argument through the map in descending order of keys.
mapAccumRWithKey :: (forall v. a -> k v -> f v -> (a, g v)) -> a -> DMap k f -> (a, DMap k g)
mapAccumRWithKey f = go
  where
    go a Tip = (a,Tip)
    go a (Bin sx kx x l r) =
                 let (a1,r') = go a r
                     (a2,x') = f a1 kx x
                     (a3,l') = go a2 l
                 in (a3,Bin sx kx x' l' r')

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
mapKeysMonotonic _ Tip = Tip
mapKeysMonotonic f (Bin sz k x l r) =
    Bin sz (f k) x (mapKeysMonotonic f l) (mapKeysMonotonic f r)

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
foldrWithKey f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = go (f kx x (go z r)) l

-- | /O(n)/. Pre-order fold.  The function will be applied from the highest
-- value to the lowest.
foldlWithKey :: (forall v. b -> k v -> f v -> b) -> b -> DMap k f -> b
foldlWithKey f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = go (f (go z l) kx x) r

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
  = [mkSome k | (k :=> _) <- assocs m]

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
fromDistinctAscList xs
  = build const (length xs) xs
  where
    -- 1) use continutations so that we use heap space instead of stack space.
    -- 2) special case for n==5 to build bushier trees.

    build :: (DMap k f -> [DSum k f] -> b) -> Int -> [DSum k f] -> b
    build c 0 xs'  = c Tip xs'
    build c 5 xs'  = case xs' of
                       ((k1:=>x1):(k2:=>x2):(k3:=>x3):(k4:=>x4):(k5:=>x5):xx)
                            -> c (bin k4 x4 (bin k2 x2 (singleton k1 x1) (singleton k3 x3)) (singleton k5 x5)) xx
                       _ -> error "fromDistinctAscList build"
    build c n xs'  = seq nr $ build (buildR nr c) nl xs'
                   where
                     nl = n `div` 2
                     nr = n - nl - 1

    buildR :: Int -> (DMap k f -> [DSum k f] -> b) -> DMap k f -> [DSum k f] -> b
    buildR n c l ((k:=>x):ys) = build (buildB l k x c) n ys
    buildR _ _ _ []           = error "fromDistinctAscList buildR []"

    buildB :: DMap k f -> k v -> f v -> (DMap k f -> a -> b) -> DMap k f -> a -> b
    buildB l k x c r zs       = c (bin k x l r) zs

{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}

-- | /O(log n)/. The expression (@'split' k map@) is a pair @(map1,map2)@ where
-- the keys in @map1@ are smaller than @k@ and the keys in @map2@ larger than @k@.
-- Any key equal to @k@ is found in neither @map1@ nor @map2@.
split :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, DMap k f)
split k = toPair . go
  where
    go :: DMap k f -> (DMap k f :*: DMap k f)
    go Tip              = (Tip :*: Tip)
    go (Bin _ kx x l r) = case gcompare k kx of
          GLT -> let !(lt :*: gt) = go l in (lt :*: combine kx x gt r)
          GGT -> let !(lt :*: gt) = go r in (combine kx x l lt :*: gt)
          GEQ -> (l :*: r)
{-# INLINABLE split #-}

-- | /O(log n)/. The expression (@'splitLookup' k map@) splits a map just
-- like 'split' but also returns @'lookup' k map@.
splitLookup :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, Maybe (f v), DMap k f)
splitLookup k = toTriple . go
  where
    go :: DMap k f -> Triple' (DMap k f) (Maybe (f v)) (DMap k f)
    go Tip              = Triple' Tip Nothing Tip
    go (Bin _ kx x l r) = case gcompare k kx of
      GLT -> let !(Triple' lt z gt) = go l in Triple' lt z (combine kx x gt r)
      GGT -> let !(Triple' lt z gt) = go r in Triple' (combine kx x l lt) z gt
      GEQ -> Triple' l (Just x) r

-- | /O(log n)/. The expression (@'splitMember' k map@) splits a map just
-- like 'split' but also returns @'member' k map@.
splitMember :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, Bool, DMap k f)
splitMember k = toTriple . go
  where
    go :: DMap k f -> Triple' (DMap k f) Bool (DMap k f)
    go Tip              = Triple' Tip False Tip
    go (Bin _ kx x l r) = case gcompare k kx of
      GLT -> let !(Triple' lt z gt) = go l in Triple' lt z (combine kx x gt r)
      GGT -> let !(Triple' lt z gt) = go r in Triple' (combine kx x l lt) z gt
      GEQ -> Triple' l True r

-- | /O(log n)/.
splitLookupWithKey :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, Maybe (k v, f v), DMap k f)
splitLookupWithKey k = toTriple . go
  where
    go :: DMap k f -> Triple' (DMap k f) (Maybe (k v, f v)) (DMap k f)
    go Tip              = Triple' Tip Nothing Tip
    go (Bin _ kx x l r) = case gcompare k kx of
      GLT -> let !(Triple' lt z gt) = go l in Triple' lt z (combine kx x gt r)
      GGT -> let !(Triple' lt z gt) = go r in Triple' (combine kx x l lt) z gt
      GEQ -> Triple' l (Just (kx, x)) r

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
showsTree showelem wide lbars rbars t
  = case t of
      Tip -> showsBars lbars . showString "|\n"
      Bin _ kx x Tip Tip
          -> showsBars lbars . showString (showelem kx x) . showString "\n"
      Bin _ kx x l r
          -> showsTree showelem wide (withBar rbars) (withEmpty rbars) r .
             showWide wide rbars .
             showsBars lbars . showString (showelem kx x) . showString "\n" .
             showWide wide lbars .
             showsTree showelem wide (withEmpty lbars) (withBar lbars) l

showsTreeHang :: (forall v. k v -> f v -> String) -> Bool -> [String] -> DMap k f -> ShowS
showsTreeHang showelem wide bars t
  = case t of
      Tip -> showsBars bars . showString "|\n"
      Bin _ kx x Tip Tip
          -> showsBars bars . showString (showelem kx x) . showString "\n"
      Bin _ kx x l r
          -> showsBars bars . showString (showelem kx x) . showString "\n" .
             showWide wide bars .
             showsTreeHang showelem wide (withBar bars) l .
             showWide wide bars .
             showsTreeHang showelem wide (withEmpty bars) r

showWide :: Bool -> [String] -> String -> String
showWide wide bars
  | wide      = showString (concat (reverse bars)) . showString "|\n"
  | otherwise = id

showsBars :: [String] -> ShowS
showsBars bars
  = case bars of
      [] -> id
      _  -> showString (concat (reverse (tail bars))) . showString node

node :: String
node           = "+--"

withBar, withEmpty :: [String] -> [String]
withBar bars   = "|  ":bars
withEmpty bars = "   ":bars

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}

-- | /O(n)/. Test if the internal map structure is valid.
valid :: GCompare k => DMap k f -> Bool
valid t
  = balanced t && ordered t && validsize t

ordered :: GCompare k => DMap k f -> Bool
ordered t
  = bounded (const True) (const True) t
  where
    bounded :: GCompare k => (Some k -> Bool) -> (Some k -> Bool) -> DMap k f -> Bool
    bounded lo hi t'
      = case t' of
          Tip              -> True
          Bin _ kx _ l r  -> lo (mkSome kx) && hi (mkSome kx) && bounded lo (< mkSome kx) l && bounded (> mkSome kx) hi r

-- | Exported only for "Debug.QuickCheck"
balanced :: DMap k f -> Bool
balanced t
  = case t of
      Tip            -> True
      Bin _ _ _ l r  -> (size l + size r <= 1 || (size l <= delta*size r && size r <= delta*size l)) &&
                        balanced l && balanced r

validsize :: DMap k f -> Bool
validsize t
  = (realsize t == Just (size t))
  where
    realsize t'
      = case t' of
          Tip            -> Just 0
          Bin sz _ _ l r -> case (realsize l,realsize r) of
                            (Just n,Just m)  | n+m+1 == sz  -> Just sz
                            _                               -> Nothing
{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}
foldlStrict :: (a -> b -> a) -> a -> [b] -> a
foldlStrict f = go
  where
    go z []     = z
    go z (x:xs) = z `seq` go (f z x) xs
