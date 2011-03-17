{-# LANGUAGE GADTs, RankNTypes #-}
module Data.Dependent.Map
    ( DMap
    , DSum(..)
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
--    , insertLookupWithKey'
    
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

import Data.Dependent.Sum
import Data.GADT.Compare
import Data.Maybe
import Data.Monoid
import Data.Unique.Tag

instance (GCompare k) => Monoid (DMap k) where
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

(!) :: GCompare k => DMap k -> k v -> v
m ! k    = find k m

-- | Same as 'difference'.
(\\) :: GCompare k => DMap k -> DMap k -> DMap k
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

member :: GCompare k => k a -> DMap k -> Bool
member k = isJust . lookup k

notMember :: GCompare k => k v -> DMap k -> Bool
notMember k m = not (member k m)

find :: GCompare k => k v -> DMap k -> v
find k m = case lookup k m of
    Nothing -> error "DMap.find: element not in the map"
    Just v  -> v

findWithDefault :: GCompare k => v -> k v -> DMap k -> v
findWithDefault def k m = case lookup k m of
    Nothing -> def
    Just v  -> v

{--------------------------------------------------------------------
  Insertion
--------------------------------------------------------------------}

insert :: GCompare k => k v -> v -> DMap k -> DMap k
insert kx x = kx `seq` go
    where
        go Tip = singleton kx x
        go (Bin sz ky y l r) = case gcompare kx ky of
            GLT -> balance ky y (go l) r
            GGT -> balance ky y l (go r)
            GEQ -> Bin sz kx x l r

insertWith :: GCompare k => (v -> v -> v) -> k v -> v -> DMap k -> DMap k
insertWith f = insertWithKey (\_ x' y' -> f x' y')

insertWith' :: GCompare k => (v -> v -> v) -> k v -> v -> DMap k -> DMap k
insertWith' f = insertWithKey' (\_ x' y' -> f x' y')

insertWithKey :: GCompare k => (k v -> v -> v -> v) -> k v -> v -> DMap k -> DMap k
insertWithKey f kx x = kx `seq` go
  where
    go Tip = singleton kx x
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> balance ky y (go l) r
            GGT -> balance ky y l (go r)
            GEQ -> Bin sy kx (f kx x y) l r

insertWithKey' :: GCompare k => (k v -> v -> v -> v) -> k v -> v -> DMap k -> DMap k
insertWithKey' f kx x = kx `seq` go
  where
    go Tip = singleton kx $! x
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> balance ky y (go l) r
            GGT -> balance ky y l (go r)
            GEQ -> let x' = f kx x y in seq x' (Bin sy kx x' l r)

insertLookupWithKey :: GCompare k => (k v -> v -> v -> v) -> k v -> v -> DMap k
                    -> (Maybe v, DMap k)
insertLookupWithKey f kx x = kx `seq` go
  where
    go Tip = (Nothing, singleton kx x)
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> let (found, l') = go l
                  in (found, balance ky y l' r)
            GGT -> let (found, r') = go r
                  in (found, balance ky y l r')
            GEQ -> (Just y, Bin sy kx (f kx x y) l r)

{--------------------------------------------------------------------
  Deletion
  [delete] is the inlined version of [deleteWith (\k x -> Nothing)]
--------------------------------------------------------------------}

delete :: GCompare k => k v -> DMap k -> DMap k
delete k = k `seq` go
  where
    go Tip = Tip
    go (Bin _ kx x l r) =
        case gcompare k kx of
            GLT -> balance kx x (go l) r
            GGT -> balance kx x l (go r)
            GEQ -> glue l r

adjust :: GCompare k => (v -> v) -> k v -> DMap k -> DMap k
adjust f = adjustWithKey (\_ x -> f x)

adjustWithKey :: GCompare k => (k v -> v -> v) -> k v -> DMap k -> DMap k
adjustWithKey f = updateWithKey (\k' x' -> Just (f k' x'))

update :: GCompare k => (v -> Maybe v) -> k v -> DMap k -> DMap k
update f = updateWithKey (\_ x -> f x)

updateWithKey :: GCompare k => (k v -> v -> Maybe v) -> k v -> DMap k -> DMap k
updateWithKey f k = k `seq` go
  where
    go Tip = Tip
    go (Bin sx kx x l r) =
        case gcompare k kx of
           GLT -> balance kx x (go l) r
           GGT -> balance kx x l (go r)
           GEQ -> case f kx x of
                   Just x' -> Bin sx kx x' l r
                   Nothing -> glue l r

updateLookupWithKey :: GCompare k => (k v -> v -> Maybe v) -> k v -> DMap k -> (Maybe v,DMap k)
updateLookupWithKey f k = k `seq` go
 where
   go Tip = (Nothing,Tip)
   go (Bin sx kx x l r) =
          case gcompare k kx of
               GLT -> let (found,l') = go l in (found,balance kx x l' r)
               GGT -> let (found,r') = go r in (found,balance kx x l r') 
               GEQ -> case f kx x of
                       Just x' -> (Just x',Bin sx kx x' l r)
                       Nothing -> (Just x,glue l r)

alter :: GCompare k => (Maybe v -> Maybe v) -> k v -> DMap k -> DMap k
alter f k = k `seq` go
  where
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

findIndex :: GCompare k => k v -> DMap k -> Int
findIndex k t
  = case lookupIndex k t of
      Nothing  -> error "Map.findIndex: element is not in the map"
      Just idx -> idx

lookupIndex :: GCompare k => k v -> DMap k -> Maybe Int
lookupIndex k = k `seq` go 0
  where
    go idx Tip  = idx `seq` Nothing
    go idx (Bin _ kx _ l r)
      = idx `seq` case gcompare k kx of
          GLT -> go idx l
          GGT -> go (idx + size l + 1) r 
          GEQ -> Just (idx + size l)

elemAt :: Int -> DMap k -> DSum k
elemAt _ Tip = error "Map.elemAt: index out of range"
elemAt i (Bin _ kx x l r)
  = case compare i sizeL of
      LT -> elemAt i l
      GT -> elemAt (i-sizeL-1) r
      EQ -> kx :=> x
  where
    sizeL = size l

updateAt :: (forall v. k v -> v -> Maybe v) -> Int -> DMap k -> DMap k
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

deleteAt :: Int -> DMap k -> DMap k
deleteAt i m
  = updateAt (\_ _ -> Nothing) i m


{--------------------------------------------------------------------
  Minimal, Maximal
--------------------------------------------------------------------}

-- | /O(log n)/. The minimal key of the map. Calls 'error' is the map is empty.
findMin :: DMap k -> DSum k
findMin (Bin _ kx x Tip _)  = kx :=> x
findMin (Bin _ _  _ l _)    = findMin l
findMin Tip                 = error "Map.findMin: empty map has no minimal element"

-- | /O(log n)/. The maximal key of the map. Calls 'error' is the map is empty.
findMax :: DMap k -> DSum k
findMax (Bin _ kx x _ Tip)  = kx :=> x
findMax (Bin _ _  _ _ r)    = findMax r
findMax Tip                 = error "Map.findMax: empty map has no maximal element"

-- | /O(log n)/. Delete the minimal key. Returns an empty map if the map is empty.
deleteMin :: DMap k -> DMap k
deleteMin (Bin _ _  _ Tip r)  = r
deleteMin (Bin _ kx x l r)    = balance kx x (deleteMin l) r
deleteMin Tip                 = Tip

-- | /O(log n)/. Delete the maximal key. Returns an empty map if the map is empty.
deleteMax :: DMap k -> DMap k
deleteMax (Bin _ _  _ l Tip)  = l
deleteMax (Bin _ kx x l r)    = balance kx x l (deleteMax r)
deleteMax Tip                 = Tip

-- | /O(log n)/. Update the value at the minimal key.
updateMinWithKey :: (forall v. k v -> v -> Maybe v) -> DMap k -> DMap k
updateMinWithKey f = go
 where
    go (Bin sx kx x Tip r) = case f kx x of
                                  Nothing -> r
                                  Just x' -> Bin sx kx x' Tip r
    go (Bin _ kx x l r)    = balance kx x (go l) r
    go Tip                 = Tip

-- | /O(log n)/. Update the value at the maximal key.
updateMaxWithKey :: (forall v. k v -> v -> Maybe v) -> DMap k -> DMap k
updateMaxWithKey f = go
 where
    go (Bin sx kx x l Tip) = case f kx x of
                              Nothing -> l
                              Just x' -> Bin sx kx x' l Tip
    go (Bin _ kx x l r)    = balance kx x l (go r)
    go Tip                 = Tip

-- | /O(log n)/. Retrieves the minimal (key,value) pair of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
minViewWithKey :: DMap k -> Maybe (DSum k, DMap k)
minViewWithKey Tip = Nothing
minViewWithKey x   = Just (deleteFindMin x)

-- | /O(log n)/. Retrieves the maximal (key,value) pair of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
maxViewWithKey :: DMap k -> Maybe (DSum k, DMap k)
maxViewWithKey Tip = Nothing
maxViewWithKey x   = Just (deleteFindMax x)

-- | /O(log n)/. Retrieves the value associated with minimal key of the
-- map, and the map stripped of that element, or 'Nothing' if passed an
-- empty map.

{--------------------------------------------------------------------
  Union. 
--------------------------------------------------------------------}

-- | The union of a list of maps:
--   (@'unions' == 'Prelude.foldl' 'union' 'empty'@).
unions :: GCompare k => [DMap k] -> DMap k
unions ts
  = foldlStrict union empty ts

-- | The union of a list of maps, with a combining operation:
--   (@'unionsWith' f == 'Prelude.foldl' ('unionWithKey' f) 'empty'@).
unionsWithKey :: GCompare k => (forall v. k v -> v -> v -> v) -> [DMap k] -> DMap k
unionsWithKey f ts
  = foldlStrict (unionWithKey f) empty ts

-- | /O(n+m)/.
-- The expression (@'union' t1 t2@) takes the left-biased union of @t1@ and @t2@. 
-- It prefers @t1@ when duplicate keys are encountered,
-- i.e. (@'union' == 'unionWith' 'const'@).
-- The implementation uses the efficient /hedge-union/ algorithm.
-- Hedge-union is more efficient on (bigset \``union`\` smallset).
union :: GCompare k => DMap k -> DMap k -> DMap k
union Tip t2  = t2
union t1 Tip  = t1
union t1 t2 = hedgeUnionL (const LT) (const GT) t1 t2

-- left-biased hedge union
hedgeUnionL :: GCompare k
            => (Key k -> Ordering) -> (Key k -> Ordering) -> DMap k -> DMap k
            -> DMap k
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
unionWithKey :: GCompare k => (forall v. k v -> v -> v -> v) -> DMap k -> DMap k -> DMap k
unionWithKey _ Tip t2  = t2
unionWithKey _ t1 Tip  = t1
unionWithKey f t1 t2 = hedgeUnionWithKey f (const LT) (const GT) t1 t2

hedgeUnionWithKey :: GCompare k
                  => (forall v. k v -> v -> v -> v)
                  -> (Key k -> Ordering) -> (Key k -> Ordering)
                  -> DMap k -> DMap k
                  -> DMap k
hedgeUnionWithKey _ _     _     t1 Tip
  = t1
hedgeUnionWithKey _ cmplo cmphi Tip (Bin _ kx x l r)
  = join kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeUnionWithKey f cmplo cmphi (Bin _ kx x l r) t2
  = join kx newx (hedgeUnionWithKey f cmplo cmpkx l lt) 
                 (hedgeUnionWithKey f cmpkx cmphi r gt)
  where
    cmpkx k     = compare (Key kx) k
    lt          = trim cmplo cmpkx t2
    (found,gt)  = trimLookupLo (Key kx) cmphi t2
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
difference :: GCompare k => DMap k -> DMap k -> DMap k
difference Tip _   = Tip
difference t1 Tip  = t1
difference t1 t2   = hedgeDiff (const LT) (const GT) t1 t2

hedgeDiff :: GCompare k
          => (Key k -> Ordering) -> (Key k -> Ordering) -> DMap k -> DMap k
          -> DMap k
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
--
-- > let f k al ar = if al == "b" then Just ((show k) ++ ":" ++ al ++ "|" ++ ar) else Nothing
-- > differenceWithKey f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (3, "B"), (10, "C")])
-- >     == singleton 3 "3:b|B"

differenceWithKey :: GCompare k => (forall v. k v -> v -> v -> Maybe v) -> DMap k -> DMap k -> DMap k
differenceWithKey _ Tip _   = Tip
differenceWithKey _ t1 Tip  = t1
differenceWithKey f t1 t2   = hedgeDiffWithKey f (const LT) (const GT) t1 t2

hedgeDiffWithKey :: GCompare k
                 => (forall v. k v -> v -> v -> Maybe v)
                 -> (Key k -> Ordering) -> (Key k -> Ordering)
                 -> DMap k -> DMap k
                 -> DMap k
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
intersection :: GCompare k => DMap k -> DMap k -> DMap k
intersection m1 m2
  = intersectionWithKey (\_ x _ -> x) m1 m2

-- | /O(n+m)/. Intersection with a combining function.
-- Intersection is more efficient on (bigset \``intersection`\` smallset).
intersectionWithKey :: GCompare k => (forall v. k v -> v -> v -> v) -> DMap k -> DMap k -> DMap k
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
isSubmapOf :: (GCompare k,EqTag k) => DMap k -> DMap k -> Bool
isSubmapOf m1 m2 = isSubmapOfBy eqTagged m1 m2

{- | /O(n+m)/.
 The expression (@'isSubmapOfBy' f t1 t2@) returns 'True' if
 all keys in @t1@ are in tree @t2@, and when @f@ returns 'True' when
 applied to their respective values. For example, the following 
 expressions are all 'True':
-}
isSubmapOfBy :: GCompare k => (forall v. k v -> k v -> v -> v -> Bool) -> DMap k -> DMap k -> Bool
isSubmapOfBy f t1 t2
  = (size t1 <= size t2) && (submap' f t1 t2)

submap' :: GCompare k => (forall v. k v -> k v -> v -> v -> Bool) -> DMap k -> DMap k -> Bool
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
isProperSubmapOf :: (GCompare k, EqTag k) => DMap k -> DMap k -> Bool
isProperSubmapOf m1 m2
  = isProperSubmapOfBy eqTagged m1 m2

{- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
 The expression (@'isProperSubmapOfBy' f m1 m2@) returns 'True' when
 @m1@ and @m2@ are not equal,
 all keys in @m1@ are in @m2@, and when @f@ returns 'True' when
 applied to their respective values. 
-}
isProperSubmapOfBy :: GCompare k => (forall v. k v -> k v -> v -> v -> Bool) -> DMap k -> DMap k -> Bool
isProperSubmapOfBy f t1 t2
  = (size t1 < size t2) && (submap' f t1 t2)

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}

-- | /O(n)/. Filter all keys\/values that satisfy the predicate.
filterWithKey :: GCompare k => (forall v. k v -> v -> Bool) -> DMap k -> DMap k
filterWithKey p = go
  where
    go Tip = Tip
    go (Bin _ kx x l r)
          | p kx x    = join kx x (go l) (go r)
          | otherwise = merge (go l) (go r)

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
partitionWithKey :: GCompare k => (forall v. k v -> v -> Bool) -> DMap k -> (DMap k,DMap k)
partitionWithKey _ Tip = (Tip,Tip)
partitionWithKey p (Bin _ kx x l r)
  | p kx x    = (join kx x l1 r1,merge l2 r2)
  | otherwise = (merge l1 r1,join kx x l2 r2)
  where
    (l1,l2) = partitionWithKey p l
    (r1,r2) = partitionWithKey p r

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
mapMaybeWithKey :: GCompare k => (forall v. k v -> v -> Maybe v) -> DMap k -> DMap k
mapMaybeWithKey f = go
  where
    go Tip = Tip
    go (Bin _ kx x l r) = case f kx x of
        Just y  -> join kx y (go l) (go r)
        Nothing -> merge (go l) (go r)

-- | /O(n)/. Map keys\/values and separate the 'Left' and 'Right' results.
mapEitherWithKey :: GCompare k =>
  (forall v. k v -> v -> Either v v) -> DMap k -> (DMap k, DMap k)
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
mapWithKey :: (forall v. k v -> v -> v) -> DMap k -> DMap k
mapWithKey f = go
  where
    go Tip = Tip
    go (Bin sx kx x l r) = Bin sx kx (f kx x) (go l) (go r)

-- | /O(n)/. The function 'mapAccumLWithKey' threads an accumulating
-- argument throught the map in ascending order of keys.
mapAccumLWithKey :: (forall v. a -> k v -> v -> (a,v)) -> a -> DMap k -> (a,DMap k)
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
mapAccumRWithKey :: (forall v. a -> k v -> v -> (a,v)) -> a -> DMap k -> (a, DMap k)
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
mapKeysWith :: GCompare k2 => (forall v. k2 v -> v -> v -> v) -> (forall v. k1 v -> k2 v) -> DMap k1 -> DMap k2
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
mapKeysMonotonic :: (forall v. k1 v -> k2 v) -> DMap k1 -> DMap k2
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
foldWithKey :: (forall v. k v -> v -> b -> b) -> b -> DMap k -> b
foldWithKey = foldrWithKey
{-# DEPRECATED foldWithKey "Use foldrWithKey instead" #-}

-- | /O(n)/. Post-order fold.  The function will be applied from the lowest
-- value to the highest.
foldrWithKey :: (forall v. k v -> v -> b -> b) -> b -> DMap k -> b
foldrWithKey f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = go (f kx x (go z r)) l

-- | /O(n)/. Pre-order fold.  The function will be applied from the highest
-- value to the lowest.
foldlWithKey :: (forall v. b -> k v -> v -> b) -> b -> DMap k -> b
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

keys  :: DMap k -> [Key k]
keys m
  = [Key k | (k :=> _) <- assocs m]

-- | /O(n)/. Return all key\/value pairs in the map in ascending key order.
assocs :: DMap k -> [DSum k]
assocs m
  = toList m

{--------------------------------------------------------------------
  Lists 
  use [foldlStrict] to reduce demand on the control-stack
--------------------------------------------------------------------}

-- | /O(n*log n)/. Build a map from a list of key\/value pairs. See also 'fromAscList'.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
fromList :: GCompare k => [DSum k] -> DMap k 
fromList xs       
  = foldlStrict ins empty xs
  where
    ins :: GCompare k => DMap k -> DSum k -> DMap k
    ins t (k :=> x) = insert k x t

-- | /O(n*log n)/. Build a map from a list of key\/value pairs with a combining function. See also 'fromAscListWithKey'.
fromListWithKey :: GCompare k => (forall v. k v -> v -> v -> v) -> [DSum k] -> DMap k 
fromListWithKey f xs 
  = foldlStrict (ins f) empty xs
  where
    ins :: GCompare k => (forall v. k v -> v -> v -> v) -> DMap k -> DSum k -> DMap k
    ins f t (k :=> x) = insertWithKey f k x t

-- | /O(n)/. Convert to a list of key\/value pairs.
toList :: DMap k -> [DSum k]
toList t      = toAscList t

-- | /O(n)/. Convert to an ascending list.
toAscList :: DMap k -> [DSum k]
toAscList t   = foldrWithKey (\k x xs -> (k :=> x):xs) [] t

-- | /O(n)/. Convert to a descending list.
toDescList :: DMap k -> [DSum k]
toDescList t  = foldlWithKey (\xs k x -> (k :=> x):xs) [] t

{--------------------------------------------------------------------
  Building trees from ascending/descending lists can be done in linear time.
  
  Note that if [xs] is ascending that: 
    fromAscList xs       == fromList xs
    fromAscListWith f xs == fromListWith f xs
--------------------------------------------------------------------}

-- | /O(n)/. Build a map from an ascending list in linear time.
-- /The precondition (input list is ascending) is not checked./
fromAscList :: GEq k => [DSum k] -> DMap k 
fromAscList xs
  = fromAscListWithKey (\_ x _ -> x) xs

-- | /O(n)/. Build a map from an ascending list in linear time with a
-- combining function for equal keys.
-- /The precondition (input list is ascending) is not checked./
fromAscListWithKey :: GEq k => (forall v. k v -> v -> v -> v) -> [DSum k] -> DMap k 
fromAscListWithKey f xs
  = fromDistinctAscList (combineEq f xs)
  where
  -- [combineEq f xs] combines equal elements with function [f] in an ordered list [xs]
  combineEq _ xs'
    = case xs' of
        []     -> []
        [x]    -> [x]
        (x:xx) -> combineEq' f x xx

  combineEq' :: GEq k => (forall v. k v -> v -> v -> v) -> DSum k -> [DSum k] -> [DSum k]
  combineEq' f z [] = [z]
  combineEq' f z@(kz :=> zz) (x@(kx :=> xx):xs') =
    case geq kx kz of
        Just Refl   -> let yy = f kx xx zz in combineEq' f (kx :=> yy) xs'
        Nothing     -> z : combineEq' f x xs'


-- | /O(n)/. Build a map from an ascending list of distinct elements in linear time.
-- /The precondition is not checked./
fromDistinctAscList :: [DSum k] -> DMap k 
fromDistinctAscList xs
  = build const (length xs) xs
  where
    -- 1) use continutations so that we use heap space instead of stack space.
    -- 2) special case for n==5 to build bushier trees. 
    
    build :: (DMap k -> [DSum k] -> b) -> Int -> [DSum k] -> b
    build c 0 xs'  = c Tip xs'
    build c 5 xs'  = case xs' of
                       ((k1:=>x1):(k2:=>x2):(k3:=>x3):(k4:=>x4):(k5:=>x5):xx) 
                            -> c (bin k4 x4 (bin k2 x2 (singleton k1 x1) (singleton k3 x3)) (singleton k5 x5)) xx
                       _ -> error "fromDistinctAscList build"
    build c n xs'  = seq nr $ build (buildR nr c) nl xs'
                   where
                     nl = n `div` 2
                     nr = n - nl - 1

    buildR :: Int -> (DMap k -> [DSum k] -> b) -> DMap k -> [DSum k] -> b
    buildR n c l ((k:=>x):ys) = build (buildB l k x c) n ys
    buildR _ _ _ []           = error "fromDistinctAscList buildR []"
    
    buildB :: DMap k -> k v -> v -> (DMap k -> a -> b) -> DMap k -> a -> b
    buildB l k x c r zs       = c (bin k x l r) zs
                      

{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}

-- | /O(log n)/. The expression (@'split' k map@) is a pair @(map1,map2)@ where
-- the keys in @map1@ are smaller than @k@ and the keys in @map2@ larger than @k@.
-- Any key equal to @k@ is found in neither @map1@ nor @map2@.
split :: GCompare k => k v -> DMap k -> (DMap k,DMap k)
split k = go
  where
    go Tip              = (Tip, Tip)
    go (Bin _ kx x l r) = case gcompare k kx of
          GLT -> let (lt,gt) = go l in (lt,join kx x gt r)
          GGT -> let (lt,gt) = go r in (join kx x l lt,gt)
          GEQ -> (l,r)

-- | /O(log n)/. The expression (@'splitLookup' k map@) splits a map just
-- like 'split' but also returns @'lookup' k map@.
splitLookup :: GCompare k => k v -> DMap k -> (DMap k,Maybe v,DMap k)
splitLookup k = go
  where
    go Tip              = (Tip,Nothing,Tip)
    go (Bin _ kx x l r) = case gcompare k kx of
      GLT -> let (lt,z,gt) = go l in (lt,z,join kx x gt r)
      GGT -> let (lt,z,gt) = go r in (join kx x l lt,z,gt)
      GEQ -> (l,Just x,r)

-- | /O(log n)/.
splitLookupWithKey :: GCompare k => k v -> DMap k -> (DMap k,Maybe (k v, v),DMap k)
splitLookupWithKey k = go
  where
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
instance EqTag k => Eq (DMap k) where
  t1 == t2  = (size t1 == size t2) && (toAscList t1 == toAscList t2)

{--------------------------------------------------------------------
  Ord 
--------------------------------------------------------------------}

instance OrdTag k => Ord (DMap k) where
    compare m1 m2 = compare (toAscList m1) (toAscList m2)

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}
-- instance (GCompare k, Read k, Read e) => Read (Map k e) where
-- #ifdef __GLASGOW_HASKELL__
--   readPrec = parens $ prec 10 $ do
--     Ident "fromList" <- lexP
--     xs <- readPrec
--     return (fromList xs)
-- 
--   readListPrec = readListPrecDefault
-- #else
--   readsPrec p = readParen (p > 10) $ \ r -> do
--     ("fromList",s) <- lex r
--     (xs,t) <- reads s
--     return (fromList xs,t)
-- #endif

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
instance ShowTag k => Show (DMap k) where
    showsPrec p m = showParen (p>10)
        ( showString "fromList "
        . showsPrec 11 (toList m)
        )

-- | /O(n)/. Show the tree that implements the map. The tree is shown
-- in a compressed, hanging format. See 'showTreeWith'.
showTree :: ShowTag k => DMap k -> String
showTree m
  = showTreeWith showElem True False m
  where
    showElem :: ShowTag k => k v -> v -> String
    showElem k x  = show (k :=> x)


{- | /O(n)/. The expression (@'showTreeWith' showelem hang wide map@) shows
 the tree that implements the map. Elements are shown using the @showElem@ function. If @hang@ is
 'True', a /hanging/ tree is shown otherwise a rotated tree is shown. If
 @wide@ is 'True', an extra wide version is shown.

>  Map> let t = fromDistinctAscList [(x,()) | x <- [1..5]]
>  Map> putStrLn $ showTreeWith (\k x -> show (k,x)) True False t
>  (4,())
>  +--(2,())
>  |  +--(1,())
>  |  +--(3,())
>  +--(5,())
>
>  Map> putStrLn $ showTreeWith (\k x -> show (k,x)) True True t
>  (4,())
>  |
>  +--(2,())
>  |  |
>  |  +--(1,())
>  |  |
>  |  +--(3,())
>  |
>  +--(5,())
>
>  Map> putStrLn $ showTreeWith (\k x -> show (k,x)) False True t
>  +--(5,())
>  |
>  (4,())
>  |
>  |  +--(3,())
>  |  |
>  +--(2,())
>     |
>     +--(1,())

-}
showTreeWith :: (forall v. k v -> v -> String) -> Bool -> Bool -> DMap k -> String
showTreeWith showelem hang wide t
  | hang      = (showsTreeHang showelem wide [] t) ""
  | otherwise = (showsTree showelem wide [] [] t) ""

showsTree :: (forall v. k v -> v -> String) -> Bool -> [String] -> [String] -> DMap k -> ShowS
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

showsTreeHang :: (forall v. k v -> v -> String) -> Bool -> [String] -> DMap k -> ShowS
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
  Typeable
--------------------------------------------------------------------}

-- #include "Typeable.h"
-- INSTANCE_TYPEABLE2(Map,mapTc,"Map")

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}
-- | /O(n)/. Test if the internal map structure is valid.
--
-- > valid (fromAscList [(3,"b"), (5,"a")]) == True
-- > valid (fromAscList [(5,"a"), (3,"b")]) == False

valid :: GCompare k => DMap k -> Bool
valid t
  = balanced t && ordered t && validsize t

ordered :: GCompare k => DMap k -> Bool
ordered t
  = bounded (const True) (const True) t
  where
    bounded :: GCompare k => (Key k -> Bool) -> (Key k -> Bool) -> DMap k -> Bool
    bounded lo hi t'
      = case t' of
          Tip              -> True
          Bin _ kx _ l r  -> (lo (Key kx)) && (hi (Key kx)) && bounded lo (< Key kx) l && bounded (> Key kx) hi r

-- | Exported only for "Debug.QuickCheck"
balanced :: DMap k -> Bool
balanced t
  = case t of
      Tip            -> True
      Bin _ _ _ l r  -> (size l + size r <= 1 || (size l <= delta*size r && size r <= delta*size l)) &&
                        balanced l && balanced r

validsize :: DMap k -> Bool
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

