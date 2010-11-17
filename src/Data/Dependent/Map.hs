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
    ) where

import Prelude hiding (null, lookup)
import qualified Data.Map as M
import Data.Dynamic
import Data.GADT.Tag
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

-- |Dependent maps: f is a GADT-like thing with a facility for 
-- rediscovering its type parameter, elements of which function as identifiers
-- tagged with the type of the thing they identify.  Real GADTs are one
-- useful instantiation of @f@, as are 'Tag's from "Data.Dependent.Tag".
newtype DMap f = DMap (M.Map (Key f) (DSum f))

-- |Internal: just a standard error message indicating a fundamental programming error.
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

-- update :: GCompare f => (a -> Maybe a) -> f a -> DMap f -> DMap f
-- update f k (DMap m) = DMap (M.update f' (Key k) m)
--     where
--         f' = fmap toDyn . f . flip fromDyn (panicKeyErr "update")
