{-# LANGUAGE GADTs, RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Safe #-}
#endif
module Data.Dependent.Map
    ( DMap
    , DSum(..), Key(..)
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
    , adjustWithKey
    , update
    , updateWithKey
    , updateLookupWithKey
    , alter

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
    , mapWithKey
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

import Prelude hiding (null, lookup)
import Data.Dependent.Map.Internal
import Data.Dependent.Map.Typeable ({- instance Typeable ... -})

import Data.Dependent.Sum
import Data.GADT.Compare
import Data.Maybe (isJust)
import Data.Monoid
import Text.Read

instance (GCompare k) => Monoid (DMap k f) where
    mempty  = empty
    mappend = union
    mconcat = unions

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
        go (Bin sz ky y l r) = case gcompare kx ky of
            GLT -> balance ky y (go l) r
            GGT -> balance ky y l (go r)
            GEQ -> Bin sz kx x l r

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
adjustWithKey f = updateWithKey (\k' x' -> Just (f k' x'))

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

-- | /O(log n)/. Update the element at /index/. Calls 'error' when an
-- invalid index is used.
updateAt :: (forall v. k v -> f v -> Maybe (f v)) -> Int -> DMap k f -> DMap k f
updateAt f i0 t = i0 `seq` go i0 t
 where
    go _ Tip  = error "Map.updateAt: index out of range"
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
findMin (Bin _ kx x Tip _)  = kx :=> x
findMin (Bin _ _  _ l _)    = findMin l
findMin Tip                 = error "Map.findMin: empty map has no minimal element"

-- | /O(log n)/. The maximal key of the map. Calls 'error' is the map is empty.
findMax :: DMap k f -> DSum k f
findMax (Bin _ kx x _ Tip)  = kx :=> x
findMax (Bin _ _  _ _ r)    = findMax r
findMax Tip                 = error "Map.findMax: empty map has no maximal element"

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

-- | /O(log n)/. Retrieves the minimal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
minViewWithKey :: DMap k f -> Maybe (DSum k f, DMap k f)
minViewWithKey Tip = Nothing
minViewWithKey x   = Just (deleteFindMin x)

-- | /O(log n)/. Retrieves the maximal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
maxViewWithKey :: DMap k f -> Maybe (DSum k f, DMap k f)
maxViewWithKey Tip = Nothing
maxViewWithKey x   = Just (deleteFindMax x)

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

-- | /O(n+m)/.
-- The expression (@'union' t1 t2@) takes the left-biased union of @t1@ and @t2@. 
-- It prefers @t1@ when duplicate keys are encountered,
-- i.e. (@'union' == 'unionWith' 'const'@).
-- The implementation uses the efficient /hedge-union/ algorithm.
-- Hedge-union is more efficient on (bigset \``union`\` smallset).
union :: GCompare k => DMap k f -> DMap k f -> DMap k f
union Tip t2  = t2
union t1 Tip  = t1
union t1 t2 = hedgeUnionL (const LT) (const GT) t1 t2

-- left-biased hedge union
hedgeUnionL :: GCompare k
            => (Key k -> Ordering) -> (Key k -> Ordering) -> DMap k f -> DMap k f
            -> DMap k f
hedgeUnionL _     _     t1 Tip
  = t1
hedgeUnionL cmplo cmphi Tip (Bin _ kx x l r)
  = join kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeUnionL cmplo cmphi (Bin _ kx x l r) t2
  = join kx x (hedgeUnionL cmplo cmpkx l (trim cmplo cmpkx t2)) 
              (hedgeUnionL cmpkx cmphi r (trim cmpkx cmphi t2))
  where
    cmpkx k  = compare (Key kx) k

{--------------------------------------------------------------------
  Union with a combining function
--------------------------------------------------------------------}

-- | /O(n+m)/.
-- Union with a combining function. The implementation uses the efficient /hedge-union/ algorithm.
-- Hedge-union is more efficient on (bigset \``union`\` smallset).
unionWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> DMap k f -> DMap k f -> DMap k f
unionWithKey _ Tip t2  = t2
unionWithKey _ t1 Tip  = t1
unionWithKey f t1 t2 = hedgeUnionWithKey f (const LT) (const GT) t1 t2

hedgeUnionWithKey :: forall k f. GCompare k
                  => (forall v. k v -> f v -> f v -> f v)
                  -> (Key k -> Ordering) -> (Key k -> Ordering)
                  -> DMap k f -> DMap k f
                  -> DMap k f
hedgeUnionWithKey _ _     _     t1 Tip
  = t1
hedgeUnionWithKey _ cmplo cmphi Tip (Bin _ kx x l r)
  = join kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeUnionWithKey f cmplo cmphi (Bin _ (kx :: k tx) x l r) t2
  = join kx newx (hedgeUnionWithKey f cmplo cmpkx l lt) 
                 (hedgeUnionWithKey f cmpkx cmphi r gt)
  where
    cmpkx k     = compare (Key kx) k
    lt          = trim cmplo cmpkx t2
    (found,gt)  = trimLookupLo (Key kx) cmphi t2
    newx :: f tx
    newx        = case found of
                    Nothing -> x
                    Just (ky :=> y) -> case geq kx ky of
                        Just Refl -> f kx x y
                        Nothing   -> error "DMap.union: inconsistent GEq instance"

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

-- | /O(n+m)/. Difference of two maps. 
-- Return elements of the first map not existing in the second map.
-- The implementation uses an efficient /hedge/ algorithm comparable with /hedge-union/.
difference :: GCompare k => DMap k f -> DMap k f -> DMap k f
difference Tip _   = Tip
difference t1 Tip  = t1
difference t1 t2   = hedgeDiff (const LT) (const GT) t1 t2

hedgeDiff :: GCompare k
          => (Key k -> Ordering) -> (Key k -> Ordering) -> DMap k f -> DMap k f
          -> DMap k f
hedgeDiff _     _     Tip _
  = Tip
hedgeDiff cmplo cmphi (Bin _ kx x l r) Tip 
  = join kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeDiff cmplo cmphi t (Bin _ kx _ l r) 
  = merge (hedgeDiff cmplo cmpkx (trim cmplo cmpkx t) l) 
          (hedgeDiff cmpkx cmphi (trim cmpkx cmphi t) r)
  where
    cmpkx k = compare (Key kx) k   

-- | /O(n+m)/. Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and both values.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@. 
-- The implementation uses an efficient /hedge/ algorithm comparable with /hedge-union/.
differenceWithKey :: GCompare k => (forall v. k v -> f v -> f v -> Maybe (f v)) -> DMap k f -> DMap k f -> DMap k f
differenceWithKey _ Tip _   = Tip
differenceWithKey _ t1 Tip  = t1
differenceWithKey f t1 t2   = hedgeDiffWithKey f (const LT) (const GT) t1 t2

hedgeDiffWithKey :: GCompare k
                 => (forall v. k v -> f v -> f v -> Maybe (f v))
                 -> (Key k -> Ordering) -> (Key k -> Ordering)
                 -> DMap k f -> DMap k f
                 -> DMap k f
hedgeDiffWithKey _ _     _     Tip _
  = Tip
hedgeDiffWithKey _ cmplo cmphi (Bin _ kx x l r) Tip
  = join kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeDiffWithKey f cmplo cmphi t (Bin _ kx x l r) 
  = case found of
      Nothing -> merge tl tr
      Just (ky :=> y) -> 
        case geq kx ky of
          Nothing -> error "DMap.difference: inconsistent GEq instance"
          Just Refl ->
            case f ky y x of
              Nothing -> merge tl tr
              Just z  -> join ky z tl tr
  where
    cmpkx k     = compare (Key kx) k   
    lt          = trim cmplo cmpkx t
    (found,gt)  = trimLookupLo (Key kx) cmphi t
    tl          = hedgeDiffWithKey f cmplo cmpkx lt l
    tr          = hedgeDiffWithKey f cmpkx cmphi gt r



{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

-- | /O(n+m)/. Intersection of two maps.
-- Return data in the first map for the keys existing in both maps.
-- (@'intersection' m1 m2 == 'intersectionWith' 'const' m1 m2@).
intersection :: GCompare k => DMap k f -> DMap k f -> DMap k f
intersection m1 m2
  = intersectionWithKey (\_ x _ -> x) m1 m2

-- | /O(n+m)/. Intersection with a combining function.
-- Intersection is more efficient on (bigset \``intersection`\` smallset).
intersectionWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> DMap k f -> DMap k f -> DMap k f
intersectionWithKey _ Tip _ = Tip
intersectionWithKey _ _ Tip = Tip
intersectionWithKey f t1@(Bin s1 k1 x1 l1 r1) t2@(Bin s2 k2 x2 l2 r2) =
   if s1 >= s2 then
      let (lt,found,gt) = splitLookupWithKey k2 t1
          tl            = intersectionWithKey f lt l2
          tr            = intersectionWithKey f gt r2
      in case found of
      Just (k,x) -> join k (f k x x2) tl tr
      Nothing -> merge tl tr
   else let (lt,found,gt) = splitLookup k1 t2
            tl            = intersectionWithKey f l1 lt
            tr            = intersectionWithKey f r1 gt
      in case found of
      Just x -> join k1 (f k1 x1 x) tl tr
      Nothing -> merge tl tr



{--------------------------------------------------------------------
  Submap
--------------------------------------------------------------------}
-- | /O(n+m)/.
-- This function is defined as (@'isSubmapOf' = 'isSubmapOfBy' 'eqTagged')@).
--
isSubmapOf :: (GCompare k, EqTag k f) => DMap k f -> DMap k f -> Bool
isSubmapOf m1 m2 = isSubmapOfBy eqTagged m1 m2

{- | /O(n+m)/.
 The expression (@'isSubmapOfBy' f t1 t2@) returns 'True' if
 all keys in @t1@ are in tree @t2@, and when @f@ returns 'True' when
 applied to their respective keys and values.
-}
isSubmapOfBy :: GCompare k => (forall v. k v -> k v -> f v -> f v -> Bool) -> DMap k f -> DMap k f -> Bool
isSubmapOfBy f t1 t2
  = (size t1 <= size t2) && (submap' f t1 t2)

submap' :: GCompare k => (forall v. k v -> k v -> f v -> f v -> Bool) -> DMap k f -> DMap k f -> Bool
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
isProperSubmapOf :: (GCompare k, EqTag k f) => DMap k f -> DMap k f -> Bool
isProperSubmapOf m1 m2
  = isProperSubmapOfBy eqTagged m1 m2

{- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
 The expression (@'isProperSubmapOfBy' f m1 m2@) returns 'True' when
 @m1@ and @m2@ are not equal,
 all keys in @m1@ are in @m2@, and when @f@ returns 'True' when
 applied to their respective keys and values. 
-}
isProperSubmapOfBy :: GCompare k => (forall v. k v -> k v -> f v -> f v -> Bool) -> DMap k f -> DMap k f -> Bool
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
    go (Bin _ kx x l r)
          | p kx x    = join kx x (go l) (go r)
          | otherwise = merge (go l) (go r)

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
partitionWithKey :: GCompare k => (forall v. k v -> f v -> Bool) -> DMap k f -> (DMap k f, DMap k f)
partitionWithKey _ Tip = (Tip,Tip)
partitionWithKey p (Bin _ kx x l r)
  | p kx x    = (join kx x l1 r1,merge l2 r2)
  | otherwise = (merge l1 r1,join kx x l2 r2)
  where
    (l1,l2) = partitionWithKey p l
    (r1,r2) = partitionWithKey p r

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
mapMaybeWithKey :: GCompare k => (forall v. k v -> f v -> Maybe (f v)) -> DMap k f -> DMap k f
mapMaybeWithKey f = go
  where
    go Tip = Tip
    go (Bin _ kx x l r) = case f kx x of
        Just y  -> join kx y (go l) (go r)
        Nothing -> merge (go l) (go r)

-- | /O(n)/. Map keys\/values and separate the 'Left' and 'Right' results.
mapEitherWithKey :: GCompare k =>
  (forall v. k v -> f v -> Either (f v) (f v)) -> DMap k f -> (DMap k f, DMap k f)
mapEitherWithKey _ Tip = (Tip, Tip)
mapEitherWithKey f (Bin _ kx x l r) = case f kx x of
  Left y  -> (join kx y l1 r1, merge l2 r2)
  Right z -> (merge l1 r1, join kx z l2 r2)
 where
    (l1,l2) = mapEitherWithKey f l
    (r1,r2) = mapEitherWithKey f r

{--------------------------------------------------------------------
  Mapping
--------------------------------------------------------------------}

-- | /O(n)/. Map a function over all values in the map.
mapWithKey :: (forall v. k v -> f v -> f v) -> DMap k f -> DMap k f
mapWithKey f = go
  where
    go Tip = Tip
    go (Bin sx kx x l r) = Bin sx kx (f kx x) (go l) (go r)

-- | /O(n)/. The function 'mapAccumLWithKey' threads an accumulating
-- argument throught the map in ascending order of keys.
mapAccumLWithKey :: (forall v. a -> k v -> f v -> (a, f v)) -> a -> DMap k f -> (a, DMap k f)
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
mapAccumRWithKey :: (forall v. a -> k v -> f v -> (a, f v)) -> a -> DMap k f -> (a, DMap k f)
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
mapKeysWith c f = fromListWithKey c . map fFirst . toList
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

keys  :: DMap k f -> [Key k]
keys m
  = [Key k | (k :=> _) <- assocs m]

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
split k = go
  where
    go :: DMap k f -> (DMap k f, DMap k f)
    go Tip              = (Tip, Tip)
    go (Bin _ kx x l r) = case gcompare k kx of
          GLT -> let (lt,gt) = go l in (lt,join kx x gt r)
          GGT -> let (lt,gt) = go r in (join kx x l lt,gt)
          GEQ -> (l,r)

-- | /O(log n)/. The expression (@'splitLookup' k map@) splits a map just
-- like 'split' but also returns @'lookup' k map@.
splitLookup :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, Maybe (f v), DMap k f)
splitLookup k = go
  where
    go :: DMap k f -> (DMap k f, Maybe (f v), DMap k f)
    go Tip              = (Tip,Nothing,Tip)
    go (Bin _ kx x l r) = case gcompare k kx of
      GLT -> let (lt,z,gt) = go l in (lt,z,join kx x gt r)
      GGT -> let (lt,z,gt) = go r in (join kx x l lt,z,gt)
      GEQ -> (l,Just x,r)

-- | /O(log n)/.
splitLookupWithKey :: forall k f v. GCompare k => k v -> DMap k f -> (DMap k f, Maybe (k v, f v), DMap k f)
splitLookupWithKey k = go
  where
    go :: DMap k f -> (DMap k f, Maybe (k v, f v), DMap k f)
    go Tip              = (Tip,Nothing,Tip)
    go (Bin _ kx x l r) = case gcompare k kx of
      GLT -> let (lt,z,gt) = go l in (lt,z,join kx x gt r)
      GGT -> let (lt,z,gt) = go r in (join kx x l lt,z,gt)
      GEQ -> (l,Just (kx, x),r)

{--------------------------------------------------------------------
  Eq converts the tree to a list. In a lazy setting, this 
  actually seems one of the faster methods to compare two trees 
  and it is certainly the simplest :-)
--------------------------------------------------------------------}
instance EqTag k f => Eq (DMap k f) where
  t1 == t2  = (size t1 == size t2) && (toAscList t1 == toAscList t2)

{--------------------------------------------------------------------
  Ord 
--------------------------------------------------------------------}

instance OrdTag k f => Ord (DMap k f) where
    compare m1 m2 = compare (toAscList m1) (toAscList m2)

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}

instance (GCompare k, ReadTag k f) => Read (DMap k f) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    return (fromList xs)

  readListPrec = readListPrecDefault

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
instance ShowTag k f => Show (DMap k f) where
    showsPrec p m = showParen (p>10)
        ( showString "fromList "
        . showsPrec 11 (toList m)
        )

-- | /O(n)/. Show the tree that implements the map. The tree is shown
-- in a compressed, hanging format. See 'showTreeWith'.
showTree :: ShowTag k f => DMap k f -> String
showTree m
  = showTreeWith showElem True False m
  where
    showElem :: ShowTag k f => k v -> f v -> String
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
    bounded :: GCompare k => (Key k -> Bool) -> (Key k -> Bool) -> DMap k f -> Bool
    bounded lo hi t'
      = case t' of
          Tip              -> True
          Bin _ kx _ l r  -> (lo (Key kx)) && (hi (Key kx)) && bounded lo (< Key kx) l && bounded (> Key kx) hi r

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

