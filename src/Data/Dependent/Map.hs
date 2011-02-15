{-# LANGUAGE GADTs #-}
module Data.Dependent.Map
    ( DMap
    , DSum(..)
    , GCompare(..), GOrdering(..)
    , empty, null, size
    , singleton
    , fromList, toList
    , member
    , insert
    , lookup, (!)
    , delete, (\\)
    , intersection
    , difference
    , union, unions
    , alter, update
    ) where

import Prelude hiding (null, lookup)
import qualified Data.Map as M
import Data.Dynamic
import Data.GADT.Compare
import Data.Dependent.Sum

-- |Internal: a 'Key' is just a wrapper for the true key type @f@ which hides
-- the associated value type and presents the key's GADT-level 'GCompare' 
-- instance as a vanilla 'Ord' instance so it can be used as the key in a
-- 'M.Map'.
data Key f where Key :: !(f a) -> Key f
instance GCompare f => Eq (Key f) where
    Key a == Key b = case gcompare a b of
        GEQ -> True
        _   -> False
instance GCompare f => Ord (Key f) where
    compare (Key a) (Key b) = case gcompare a b of
        GLT -> LT
        GEQ -> EQ
        GGT -> GT

-- |Dependent maps: @f@ is a type with one type parameter (typically a phantom 
-- type) and a facility for rediscovering that type parameter.  Values of type
-- @f a@ function as map keys tagged with the type of the entries they identify.
-- Real GADTs are one useful instantiation of @f@, as is 'Tag' from
-- "Data.Unique.Tag" (in the \"prim-uniq\" package).
--
-- Semantically, @'DMap' f@ is equivalent to a set of @'DSum' f@ where no two
-- elements have the same tag.
--
-- More informally, 'DMap' is to dependent products as 'M.Map' is to functions.
-- Thus it could also be thought of as a partial (in the sense of \"partial
-- function\") dependent product (a dependent product over @f@ is like a
-- function of type @forall a. f a -> a@).
newtype DMap f = DMap (M.Map (Key f) (DSum f))

-- | [internal] Just a standard error message indicating a fundamental programming error.
panicKeyErr :: String -> a
panicKeyErr str = error ("Data.Dependent.Map." ++ str ++ ": key not present or type error")

empty :: DMap f
empty = DMap M.empty

singleton :: GCompare f => f a -> a -> DMap f
singleton key thing = insert key thing empty

null :: DMap f -> Bool
null (DMap m) = M.null m

size :: DMap f -> Int
size (DMap m) = M.size m

fromList :: GCompare f => [DSum f] -> DMap f
fromList [] = empty
fromList ((k :=> v) : rest) = insert k v (fromList rest)

toList :: DMap f -> [DSum f]
toList (DMap m) = map snd (M.toList m)

member :: GCompare f => f a -> DMap f -> Bool
member k (DMap m) = M.member (Key k) m

insert :: GCompare f => f a -> a -> DMap f -> DMap f
insert k thing (DMap m) = DMap (M.insert (Key k) (k :=> thing) m)

-- insertWith :: GCompare f => (a -> a -> a) -> f a -> a -> DMap f -> DMap f
-- insertWith f k thing (DMap m) = DMap (M.insertWith f' (Key k) (DSum k thing) m)
--     where
-- --        e = panicKeyErr "insertWith"
--         f' :: GCompare f => DSum f -> DSum f -> DSum f
--         f' (DSum k1 x) (DSum k2 y) = case gcompare k1 k2 of
--             GEQ -> case gcompare k k1 of
--                 GEQ -> DSum k (f x y)

lookup :: GCompare f => f a -> DMap f -> Maybe a
lookup k (DMap m) = do
    k1 :=> v <- M.lookup (Key k) m
    GEQ <- geq k k1
    return v

delete :: GCompare f => f a -> DMap f -> DMap f
delete k (DMap m) = DMap (M.delete (Key k) m)

(!) :: GCompare f => DMap f -> f a -> a
DMap m ! k = case m M.! Key k of
    k1 :=> v -> case gcompare k k1 of
        GEQ -> v
        _ -> panicKeyErr "!"

(\\) :: GCompare f => DMap f -> DMap f -> DMap f
DMap m1 \\ DMap m2 = DMap (m1 M.\\ m2)

intersection :: GCompare f => DMap f -> DMap f -> DMap f
intersection (DMap m1) (DMap m2) = DMap (M.intersection m1 m2)

difference :: GCompare f => DMap f -> DMap f -> DMap f
difference (DMap m1) (DMap m2) = DMap (M.difference m1 m2)

union :: GCompare f => DMap f -> DMap f -> DMap f
union (DMap m1) (DMap m2) = DMap (M.union m1 m2)

unions :: GCompare f => [DMap f] -> DMap f
unions dmaps = DMap $ M.unions [ m | DMap m <- dmaps]

-- TODO: I expect Data.Map.alter is more efficient.  Figure out the necessary
-- type gymnastics to make this work as a simple wrapper to that function.
alter :: GCompare f => (Maybe a -> Maybe a) -> f a -> DMap f -> DMap f
alter f k m = maybe (delete k) (insert k) (f (lookup k m)) m

update :: GCompare f => (a -> Maybe a) -> f a -> DMap f -> DMap f
update f = alter (maybe Nothing f)
