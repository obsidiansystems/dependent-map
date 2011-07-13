{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Dependent.Map.Internal where

import Data.Dependent.Sum
import Data.GADT.Compare
import Data.GADT.Show

-- |A 'Key' is just a wrapper for the true key type @f@ which hides
-- the associated value type and presents the key's GADT-level 'GCompare' 
-- instance as a vanilla 'Ord' instance so it can be used in cases where we
-- don't care about the associated value.
data Key f where Key :: !(f a) -> Key f
instance GEq f => Eq (Key f) where
    Key a == Key b = maybe False (const True) (geq a b)
instance GCompare f => Ord (Key f) where
    compare (Key a) (Key b) = weakenOrdering (gcompare a b)

instance GShow f => Show (Key f) where
    showsPrec p (Key k) = showParen (p>10)
        ( showString "Key "
        . gshowsPrec 11 k
        )
instance GRead f => Read (Key f) where
    readsPrec p = readParen (p>10) $ \s ->
        [ (withTag Key, rest')
        | let (con, rest) = splitAt 4 s
        , con == "Key "
        , (withTag, rest') <- greadsPrec 11 rest
        ]

-- |Dependent maps: f is a GADT-like thing with a facility for 
-- rediscovering its type parameter, elements of which function as identifiers
-- tagged with the type of the thing they identify.  Real GADTs are one
-- useful instantiation of @f@, as are 'Tag's from "Data.Dependent.Tag".
--
-- Semantically, @'DMap' f@ is equivalent to a set of @'DSum' f@ where no two
-- elements have the same tag.
--
-- More informally, 'DMap' is to dependent products as 'M.Map' is to @(->)@.
-- Thus it could also be thought of as a partial (in the sense of \"partial
-- function\") dependent product.
data DMap k where
    Tip :: DMap k
    Bin ::
        { sz    :: !Int
        , key   :: !(k v)
        , value :: v
        , left  :: !(DMap k)
        , right :: !(DMap k)
        } -> DMap k

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | /O(1)/. The empty map.
--
-- > empty      == fromList []
-- > size empty == 0
empty :: DMap k
empty = Tip

-- | /O(1)/. A map with a single element.
--
-- > singleton 1 'a'        == fromList [(1, 'a')]
-- > size (singleton 1 'a') == 1
singleton :: k v -> v -> DMap k
singleton k x = Bin 1 k x Tip Tip

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(1)/. Is the map empty?
null :: DMap k -> Bool
null Tip    = True
null Bin{}  = False

-- | /O(1)/. The number of elements in the map.
size :: DMap k -> Int
size Tip            = 0
size Bin{sz = n}    = n

-- | /O(log n)/. Lookup the value at a key in the map.
--
-- The function will return the corresponding value as @('Just' value)@,
-- or 'Nothing' if the key isn't in the map.
lookup :: forall k v. GCompare k => k v -> DMap k -> Maybe v
lookup k = k `seq` go
    where
        go :: DMap k -> Maybe v
        go Tip = Nothing
        go (Bin _ kx x l r) = 
            case gcompare k kx of
                GLT -> go l
                GGT -> go r
                GEQ -> Just x

lookupAssoc :: forall k v. GCompare k => Key k -> DMap k -> Maybe (DSum k)
lookupAssoc (Key k) = k `seq` go
  where
    go :: DMap k -> Maybe (DSum k)
    go Tip = Nothing
    go (Bin _ kx x l r) =
        case gcompare k kx of
            GLT -> go l
            GGT -> go r
            GEQ -> Just (kx :=> x)

{--------------------------------------------------------------------
  Utility functions that maintain the balance properties of the tree.
  All constructors assume that all values in [l] < [k] and all values
  in [r] > [k], and that [l] and [r] are valid trees.
  
  In order of sophistication:
    [Bin sz k x l r]  The type constructor.
    [bin k x l r]     Maintains the correct size, assumes that both [l]
                      and [r] are balanced with respect to each other.
    [balance k x l r] Restores the balance and size.
                      Assumes that the original tree was balanced and
                      that [l] or [r] has changed by at most one element.
    [join k x l r]    Restores balance and size. 

  Furthermore, we can construct a new tree from two trees. Both operations
  assume that all values in [l] < all values in [r] and that [l] and [r]
  are valid:
    [glue l r]        Glues [l] and [r] together. Assumes that [l] and
                      [r] are already balanced with respect to each other.
    [merge l r]       Merges two trees and restores balance.

  Note: in contrast to Adam's paper, we use (<=) comparisons instead
  of (<) comparisons in [join], [merge] and [balance]. 
  Quickcheck (on [difference]) showed that this was necessary in order 
  to maintain the invariants. It is quite unsatisfactory that I haven't 
  been able to find out why this is actually the case! Fortunately, it 
  doesn't hurt to be a bit more conservative.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Join 
--------------------------------------------------------------------}
join :: GCompare k => k v -> v -> DMap k -> DMap k -> DMap k
join kx x Tip r  = insertMin kx x r
join kx x l Tip  = insertMax kx x l
join kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  | delta*sizeL <= sizeR  = balance kz z (join kx x l lz) rz
  | delta*sizeR <= sizeL  = balance ky y ly (join kx x ry r)
  | otherwise             = bin kx x l r


-- insertMin and insertMax don't perform potentially expensive comparisons.
insertMax,insertMin :: k v -> v -> DMap k -> DMap k
insertMax kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balance ky y l (insertMax kx x r)
             
insertMin kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balance ky y (insertMin kx x l) r
             
{--------------------------------------------------------------------
  [merge l r]: merges two trees.
--------------------------------------------------------------------}
merge :: DMap k -> DMap k -> DMap k
merge Tip r   = r
merge l Tip   = l
merge l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry)
  | delta*sizeL <= sizeR = balance ky y (merge l ly) ry
  | delta*sizeR <= sizeL = balance kx x lx (merge rx r)
  | otherwise            = glue l r

{--------------------------------------------------------------------
  [glue l r]: glues two trees together.
  Assumes that [l] and [r] are already balanced with respect to each other.
--------------------------------------------------------------------}
glue :: DMap k -> DMap k -> DMap k
glue Tip r = r
glue l Tip = l
glue l r   
  | size l > size r = case deleteFindMax l of (km :=> m,l') -> balance km m l' r
  | otherwise       = case deleteFindMin r of (km :=> m,r') -> balance km m l r'

-- | /O(log n)/. Delete and find the minimal element.
--
-- > deleteFindMin (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((3,"b"), fromList[(5,"a"), (10,"c")]) 
-- > deleteFindMin                                            Error: can not return the minimal element of an empty map

deleteFindMin :: DMap k -> (DSum k, DMap k)
deleteFindMin t 
  = case t of
      Bin _ k x Tip r -> (k :=> x ,r)
      Bin _ k x l r   -> let (km,l') = deleteFindMin l in (km,balance k x l' r)
      Tip             -> (error "Map.deleteFindMin: can not return the minimal element of an empty map", Tip)

-- | /O(log n)/. Delete and find the maximal element.
--
-- > deleteFindMax (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((10,"c"), fromList [(3,"b"), (5,"a")])
-- > deleteFindMax empty                                      Error: can not return the maximal element of an empty map

deleteFindMax :: DMap k -> (DSum k, DMap k)
deleteFindMax t
  = case t of
      Bin _ k x l Tip -> (k :=> x,l)
      Bin _ k x l r   -> let (km,r') = deleteFindMax r in (km,balance k x l r')
      Tip             -> (error "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)


{--------------------------------------------------------------------
  [balance l x r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper.
  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It is correspondes with the inverse
          of $\alpha$ in Adam's article.

  Note that:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.
  
  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  - Balancing is automatic for random data and a balancing
    scheme is only necessary to avoid pathological worst cases.
    Almost any choice will do, and in practice, a rather large
    [delta] may perform better than smaller one.

  Note: in contrast to Adam's paper, we use a ratio of (at least) [2]
  to decide whether a single or double rotation is needed. Allthough
  he actually proves that this ratio is needed to maintain the
  invariants, his implementation uses an invalid ratio of [1].
--------------------------------------------------------------------}
delta,ratio :: Int
delta = 4
ratio = 2

balance :: k v -> v -> DMap k -> DMap k -> DMap k
balance k x l r
  | sizeL + sizeR <= 1    = Bin sizeX k x l r
  | sizeR >= delta*sizeL  = rotateL k x l r
  | sizeL >= delta*sizeR  = rotateR k x l r
  | otherwise             = Bin sizeX k x l r
  where
    sizeL = size l
    sizeR = size r
    sizeX = sizeL + sizeR + 1

-- rotate
rotateL :: k v -> v -> DMap k -> DMap k -> DMap k
rotateL k x l r@(Bin _ _ _ ly ry)
  | size ly < ratio*size ry = singleL k x l r
  | otherwise               = doubleL k x l r
rotateL _ _ _ Tip = error "rotateL Tip"

rotateR :: k v -> v -> DMap k -> DMap k -> DMap k
rotateR k x l@(Bin _ _ _ ly ry) r
  | size ry < ratio*size ly = singleR k x l r
  | otherwise               = doubleR k x l r
rotateR _ _ Tip _ = error "rotateR Tip"

-- basic rotations
singleL, singleR :: k v -> v -> DMap k -> DMap k -> DMap k
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3
singleL _ _ _ Tip = error "singleL Tip"
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)
singleR _ _ Tip _ = error "singleR Tip"

doubleL, doubleR :: k v -> v -> DMap k -> DMap k -> DMap k
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
doubleL _ _ _ _ = error "doubleL"
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
doubleR _ _ _ _ = error "doubleR"

{--------------------------------------------------------------------
  The bin constructor maintains the size of the tree
--------------------------------------------------------------------}
bin :: k v -> v -> DMap k -> DMap k -> DMap k
bin k x l r
  = Bin (size l + size r + 1) k x l r

{--------------------------------------------------------------------
  Utility functions that return sub-ranges of the original
  tree. Some functions take a comparison function as argument to
  allow comparisons against infinite values. A function [cmplo k]
  should be read as [compare lo k].

  [trim cmplo cmphi t]  A tree that is either empty or where [cmplo k == LT]
                        and [cmphi k == GT] for the key [k] of the root.
  [filterGt cmp t]      A tree where for all keys [k]. [cmp k == LT]
  [filterLt cmp t]      A tree where for all keys [k]. [cmp k == GT]

  [split k t]           Returns two trees [l] and [r] where all keys
                        in [l] are <[k] and all keys in [r] are >[k].
  [splitLookup k t]     Just like [split] but also returns whether [k]
                        was found in the tree.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  [trim lo hi t] trims away all subtrees that surely contain no
  values between the range [lo] to [hi]. The returned tree is either
  empty or the key of the root is between @lo@ and @hi@.
--------------------------------------------------------------------}
trim :: (Key k -> Ordering) -> (Key k -> Ordering) -> DMap k -> DMap k
trim _     _     Tip = Tip
trim cmplo cmphi t@(Bin _ kx _ l r)
  = case cmplo (Key kx) of
      LT -> case cmphi (Key kx) of
              GT -> t
              _  -> trim cmplo cmphi l
      _  -> trim cmplo cmphi r
              
trimLookupLo :: GCompare k => Key k -> (Key k -> Ordering) -> DMap k -> (Maybe (DSum k), DMap k)
trimLookupLo _  _     Tip = (Nothing,Tip)
trimLookupLo lo cmphi t@(Bin _ kx x l r)
  = case compare lo (Key kx) of
      LT -> case cmphi (Key kx) of
              GT -> (lookupAssoc lo t, t)
              _  -> trimLookupLo lo cmphi l
      GT -> trimLookupLo lo cmphi r
      EQ -> (Just (kx :=> x),trim (compare lo) cmphi r)


{--------------------------------------------------------------------
  [filterGt k t] filter all keys >[k] from tree [t]
  [filterLt k t] filter all keys <[k] from tree [t]
--------------------------------------------------------------------}
filterGt :: GCompare k => (Key k -> Ordering) -> DMap k -> DMap k
filterGt cmp = go
  where
    go Tip              = Tip
    go (Bin _ kx x l r) = case cmp (Key kx) of
              LT -> join kx x (go l) r
              GT -> go r
              EQ -> r

filterLt :: GCompare k => (Key k -> Ordering) -> DMap k -> DMap k
filterLt cmp = go
  where
    go Tip              = Tip
    go (Bin _ kx x l r) = case cmp (Key kx) of
          LT -> go l
          GT -> join kx x l (go r)
          EQ -> l
