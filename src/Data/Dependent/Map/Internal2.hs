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
module Data.Dependent.Map.Internal2 where

import Prelude hiding (null, lookup, map)
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative(..), (<$>))
#endif
import Data.Dependent.Map.Internal
#if !MIN_VERSION_base(4,7,0)
import Data.Dependent.Map.Typeable ({- instance Typeable ... -})
#endif
import Data.Dependent.Map.PtrEquality

import Data.Dependent.Sum
import Data.GADT.Compare
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NEL
import Data.Some

{--------------------------------------------------------------------
  Insertion Worker Builders
--------------------------------------------------------------------}

makeInsert
    :: forall k f v
    .  GCompare k
    => k v
    -> f v
    -> DMap k f
    -> NonEmptyDMap k f
makeInsert kx x = kx `seq` go
    where
        go :: DMap k f -> NonEmptyDMap k f
        go Tip = singletonNE kx x
        go (Bin' t@(NonEmptyDMap sz ky y l r)) = case gcompare kx ky of
            GLT -> let !l' = go l
                   in case l of
                        Bin' nel | l' `ptrEq` nel -> t
                        _ -> balanceNEL ky y l' r
            GGT -> let !r' = go r
                   in case r of
                        Bin' ner | r' `ptrEq` ner -> t
                        _ -> balanceNER ky y l r'
            GEQ
              | kx `ptrEq` ky && x `ptrEq` y -> t
              | otherwise -> NonEmptyDMap sz kx x l r

makeInsertR
  :: forall k f v
  . GCompare k
  => k v
  -> f v
  -> DMap k f
  -> NonEmptyDMap k f
makeInsertR kx x = kx `seq` go
    where
        go :: DMap k f -> NonEmptyDMap k f
        go Tip = singletonNE kx x
        go (Bin' t@(NonEmptyDMap sz ky y l r)) = case gcompare kx ky of
            GLT -> let !l' = go l
                   in case l of
                        Bin' nel | l' `ptrEq` nel -> t
                        _ -> balanceNEL ky y l' r
            GGT -> let !r' = go r
                   in case r of
                        Bin' ner | r' `ptrEq` ner -> t
                        _ -> balanceNER ky y l r'
            GEQ -> t

makeInsertWithKey
  :: forall k f v
  .  GCompare k
  => (k v -> f v -> f v -> f v)
  -> k v
  -> f v
  -> DMap k f
  -> NonEmptyDMap k f
makeInsertWithKey f kx x = kx `seq` go
  where
    go :: DMap k f -> NonEmptyDMap k f
    go Tip = singletonNE kx x
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> balanceNEL ky y (go l) r
            GGT -> balanceNER ky y l (go r)
            GEQ -> NonEmptyDMap sy kx (f kx x y) l r

makeInsertWithKey'
  :: forall k f v
  .  GCompare k
  => (k v -> f v -> f v -> f v)
  -> k v
  -> f v
  -> DMap k f
  -> NonEmptyDMap k f
makeInsertWithKey' f kx x = kx `seq` go
  where
    go :: DMap k f -> NonEmptyDMap k f
    go Tip = singletonNE kx $! x
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> balanceNEL ky y (go l) r
            GGT -> balanceNER ky y l (go r)
            GEQ -> let x' = f kx x y in seq x' (NonEmptyDMap sy kx x' l r)

makeInsertLookupWithKey
  :: forall k f v
  .  GCompare k
  => (k v -> f v -> f v -> f v)
  -> k v
  -> f v
  -> DMap k f
  -> (Maybe (f v), NonEmptyDMap k f)
makeInsertLookupWithKey f kx x = kx `seq` go
  where
    go :: DMap k f -> (Maybe (f v), NonEmptyDMap k f)
    go Tip = (Nothing, singletonNE kx x)
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> let (found, l') = go l
                  in (found, balanceNEL ky y l' r)
            GGT -> let (found, r') = go r
                  in (found, balanceNER ky y l r')
            GEQ -> (Just y, NonEmptyDMap sy kx (f kx x y) l r)

makeInsertLookupWithKey'
  :: forall k f v
  .  GCompare k
  => (k v -> f v -> f v -> f v)
  -> k v
  -> f v
  -> DMap k f
  -> (Maybe (f v), NonEmptyDMap k f)
makeInsertLookupWithKey' f kx x = kx `seq` go
  where
    go :: DMap k f -> (Maybe (f v), NonEmptyDMap k f)
    go Tip = x `seq` (Nothing, singletonNE kx x)
    go (Bin sy ky y l r) =
        case gcompare kx ky of
            GLT -> let (found, l') = go l
                  in (found, balanceNEL ky y l' r)
            GGT -> let (found, r') = go r
                  in (found, balanceNER ky y l r')
            GEQ -> let x' = f kx x y in x' `seq` (Just y, NonEmptyDMap sy kx x' l r)

{--------------------------------------------------------------------
  Deletion Worker Builders
--------------------------------------------------------------------}

makeDelete
  :: forall k f v
  .  GCompare k
  => k v
  -> ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> Maybe (NonEmptyDMap k f)
     )
makeDelete k = (k `seq` go, k `seq` nonEmpty . go')
  where
    go :: DMap k f -> DMap k f
    go Tip = Tip
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> DMap k f
    go' (NonEmptyDMap _ kx x l r) =
        case gcompare k kx of
            GLT -> Bin' $! balanceE kx x (go l) r
            GGT -> Bin' $! balanceE kx x l (go r)
            GEQ -> glueE l r

makeAdjustF
  :: forall f k v g
  .  (GCompare k, Applicative f)
  => (g v -> f (g v))
  -> k v
  -> ( DMap k g -> f (DMap k g)
     , NonEmptyDMap k g -> f (NonEmptyDMap k g)
     )
makeAdjustF f k = (k `seq` go, k `seq` go')
  where
    go :: DMap k g -> f (DMap k g)
    go Tip = pure Tip
    go (Bin' ne) = Bin' <$> go' ne

    go' :: NonEmptyDMap k g -> f (NonEmptyDMap k g)
    go' (NonEmptyDMap sx kx x l r) =
      case gcompare k kx of
        GLT -> NonEmptyDMap sx kx x <$> go l <*> pure r
        GGT -> NonEmptyDMap sx kx x l <$> go r
        GEQ -> NonEmptyDMap sx kx <$> f x <*> pure l <*> pure r

makeAdjustWithKey
  :: forall k f v
  .  GCompare k
  => (k v -> f v -> f v)
  -> k v
  -> ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> NonEmptyDMap k f
     )
makeAdjustWithKey f k = (k `seq` go, k `seq` go')
  where
    go :: DMap k f -> DMap k f
    go Tip = Tip
    go (Bin' ne) = Bin' $! go' ne

    go' :: NonEmptyDMap k f -> NonEmptyDMap k f
    go' (NonEmptyDMap sx kx x l r) =
      case gcompare k kx of
        GLT -> NonEmptyDMap sx kx x (go l) r
        GGT -> NonEmptyDMap sx kx x l (go r)
        GEQ -> NonEmptyDMap sx kx (f kx x) l r

makeAdjustWithKey'
  :: forall k f v
  .  GCompare k
  => (k v -> f v -> f v)
  -> k v
  -> ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> NonEmptyDMap k f
     )
makeAdjustWithKey' f k = (k `seq` go, k `seq` go')
  where
    go :: DMap k f -> DMap k f
    go Tip = Tip
    go (Bin' ne) = Bin' $! go' ne

    go' :: NonEmptyDMap k f -> NonEmptyDMap k f
    go' (NonEmptyDMap sx kx x l r) =
      case gcompare k kx of
        GLT -> NonEmptyDMap sx kx x (go l) r
        GGT -> NonEmptyDMap sx kx x l (go r)
        GEQ -> let !x' = f kx x in NonEmptyDMap sx kx x' l r

makeUpdateWithKey
  :: forall k f v
  .  GCompare k
  => (k v -> f v -> Maybe (f v))
  -> k v
  -> ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> Maybe (NonEmptyDMap k f)
     )
makeUpdateWithKey f k = (k `seq` go, k `seq` nonEmpty . go')
  where
    go :: DMap k f -> DMap k f
    go Tip = Tip
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> DMap k f
    go' (NonEmptyDMap sx kx x l r) =
        case gcompare k kx of
           GLT -> Bin' $! balanceE kx x (go l) r
           GGT -> Bin' $! balanceE kx x l (go r)
           GEQ -> case f kx x of
                   Just x' -> Bin sx kx x' l r
                   Nothing -> glueE l r

makeUpdateLookupWithKey
  :: forall k f v
  .  GCompare k
  => (k v -> f v -> Maybe (f v))
  -> k v
  -> ( DMap k f -> (Maybe (f v), DMap k f)
     , NonEmptyDMap k f -> (Maybe (f v), Maybe (NonEmptyDMap k f))
     )
makeUpdateLookupWithKey f k = (k `seq` go, k `seq` fmap nonEmpty . go')
  where
    go :: DMap k f -> (Maybe (f v), DMap k f)
    go Tip = (Nothing, Tip)
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> (Maybe (f v), DMap k f)
    go' (NonEmptyDMap sx kx x l r) =
           case gcompare k kx of
                GLT -> let (found,l') = go l in (found,Bin' $! balanceE kx x l' r)
                GGT -> let (found,r') = go r in (found,Bin' $! balanceE kx x l r')
                GEQ -> case f kx x of
                        Just x' -> (Just x', Bin sx kx x' l r)
                        Nothing -> (Just x, glueE l r)

makeAlter
  :: forall k f v
  .  GCompare k
  => (Maybe (f v) -> Maybe (f v))
  -> k v
  -> ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> Maybe (NonEmptyDMap k f)
     )
makeAlter f k = (k `seq` go, k `seq` nonEmpty . go')
  where
    go :: DMap k f -> DMap k f
    go Tip = case f Nothing of
               Nothing -> Tip
               Just x  -> singletonE k x
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> DMap k f
    go' (NonEmptyDMap sx kx x l r) = case gcompare k kx of
               GLT -> Bin' $! balanceE kx x (go l) r
               GGT -> Bin' $! balanceE kx x l (go r)
               GEQ -> case f (Just x) of
                       Just x' -> Bin sx kx x' l r
                       Nothing -> glueE l r

{--------------------------------------------------------------------
  Indexing Worker Builders
--------------------------------------------------------------------}

makeAlterF
  :: forall k f v g
  .  (GCompare  k, Functor f)
  => k v
  -> (Maybe (g v) -> f (Maybe (g v)))
  -> ( DMap k g -> f (DMap k g)
     , NonEmptyDMap k g -> f (Maybe (NonEmptyDMap k g))
     )
makeAlterF k f = (go, fmap nonEmpty . go')
  where
    go :: DMap k g -> f (DMap k g)
    go Tip = maybe Tip (singletonE k) <$> f Nothing
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k g -> f (DMap k g)
    go' (NonEmptyDMap sx kx x l r) = case gcompare k kx of
      GLT -> (\l' -> Bin' $! balanceE kx x l' r) <$> go l
      GGT -> (\r' -> Bin' $! balanceE kx x l r') <$> go r
      GEQ -> maybe (glueE l r) (\x' -> Bin sx kx x' l r) <$> f (Just x)

makeLookupIndex
  :: forall k f v
  .  GCompare k
  => k v
  -> ( DMap k f -> Maybe Int
     , NonEmptyDMap k f -> Maybe Int
     )
makeLookupIndex k = (k `seq` go 0, k `seq` go' 0)
  where
    go :: Int -> DMap k f -> Maybe Int
    go !idx Tip  = idx `seq` Nothing
    go !idx (Bin' ne) = go' idx ne

    go' :: Int -> NonEmptyDMap k f -> Maybe Int
    go' !idx (NonEmptyDMap _ kx _ l r)
      = case gcompare k kx of
          GLT -> go idx l
          GGT -> go (idx + sizeE l + 1) r
          GEQ -> Just (idx + sizeE l)

makElemAt
  :: ( Int -> DMap k f -> DSum k f
     , Int -> NonEmptyDMap k f -> DSum k f
     )
makElemAt = (go, go')
  where
    go _ Tip = error "Map.elemAt: index out of range"
    go i (Bin' ne) = go' i ne

    go' :: Int -> NonEmptyDMap k f -> DSum k f
    go' i (NonEmptyDMap _ kx x l r)
      = case compare i sizeL of
          LT -> go i l
          GT -> go (i-sizeL-1) r
          EQ -> kx :=> x
      where
        sizeL = sizeE l

makeUpdateAt
  :: forall k f v
  .  (forall v. k v -> f v -> Maybe (f v))
  -> Int
  -> ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> Maybe (NonEmptyDMap k f)
     )
makeUpdateAt f i0 = (i0 `seq` go i0, i0 `seq` nonEmpty . go' i0)
  where
    go :: Int -> DMap k f -> DMap k f
    go _ Tip  = Tip
    go i (Bin' ne) = go' i ne

    go' :: Int -> NonEmptyDMap k f -> DMap k f
    go' i (NonEmptyDMap sx kx x l r) = case compare i sizeL of
      LT -> Bin' $! balanceE kx x (go i l) r
      GT -> Bin' $! balanceE kx x l (go (i-sizeL-1) r)
      EQ -> case f kx x of
              Just x' -> Bin sx kx x' l r
              Nothing -> glueE l r
      where
        sizeL = sizeE l

{--------------------------------------------------------------------
  Minimal, Maximal Worker Builders
--------------------------------------------------------------------}

makeLookupMin
  :: ( DMap k f -> Maybe (DSum k f)
     , NonEmptyDMap k f -> DSum k f
     )
makeLookupMin = (go, go')
  where
    go m = case m of
      Tip -> Nothing
      Bin _ kx x l _ -> Just $! goInner kx x l

    go' (NonEmptyDMap _ kx x l _) = goInner kx x l

    goInner :: k v -> f v -> DMap k f -> DSum k f
    goInner kx x Tip = kx :=> x
    goInner kx x (Bin' ne) = goInner' kx x ne

    goInner' :: k v -> f v -> NonEmptyDMap k f -> DSum k f
    goInner' _  _ (NonEmptyDMap _ kx x l _) = goInner kx x l

makeLookupMax
  :: ( DMap k f -> Maybe (DSum k f)
     , NonEmptyDMap k f -> DSum k f
     )
makeLookupMax = (go, go')
  where
    go m = case m of
      Tip -> Nothing
      Bin _ kx x _ r -> Just $! goInner kx x r

    go' (NonEmptyDMap _ kx x _ r) = goInner kx x r

    goInner :: k v -> f v -> DMap k f -> DSum k f
    goInner kx x Tip = kx :=> x
    goInner kx x (Bin' ne) = goInner' kx x ne

    goInner' :: k v -> f v -> NonEmptyDMap k f -> DSum k f
    goInner' _  _ (NonEmptyDMap _ kx x _ r) = goInner kx x r

makeDeleteMin
  :: forall k f
  .  ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> Maybe (NonEmptyDMap k f)
     )
makeDeleteMin = (go, nonEmpty . go')
  where
    go :: DMap k f -> DMap k f
    go Tip       = Tip
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> DMap k f
    go' (NonEmptyDMap _ _  _ Tip r) = r
    go' (NonEmptyDMap _ kx x l r)   = Bin' $! balanceE kx x (go l) r

makeDeleteMax
  :: forall k f
  .  ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> Maybe (NonEmptyDMap k f)
     )
makeDeleteMax = (go, nonEmpty . go')
  where
    go :: DMap k f -> DMap k f
    go Tip       = Tip
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> DMap k f
    go' (NonEmptyDMap _ _  _ l Tip) = l
    go' (NonEmptyDMap _ kx x l r)   = Bin' $! balanceE kx x l (go r)


-- | /O(log n)/. Update the value at the minimal key.
makeUpdateMinWithKey
  :: (forall v. k v -> f v -> Maybe (f v))
  -> ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> Maybe (NonEmptyDMap k f))
makeUpdateMinWithKey f = (go, nonEmpty . go')
 where
    go Tip       = Tip
    go (Bin' ne) = go' ne

    go' (NonEmptyDMap sx kx x Tip r) = case f kx x of
                                  Nothing -> r
                                  Just x' -> Bin sx kx x' Tip r
    go' (NonEmptyDMap _ kx x l r)    = Bin' $! balanceE kx x (go l) r

makeUpdateMaxWithKey
  :: (forall v. k v -> f v -> Maybe (f v))
  -> ( DMap k f -> DMap k f
     , NonEmptyDMap k f -> Maybe (NonEmptyDMap k f))
makeUpdateMaxWithKey f = (go, nonEmpty . go')
 where
    go Tip                 = Tip
    go (Bin' ne) = go' ne

    go' (NonEmptyDMap sx kx x l Tip) = case f kx x of
                              Nothing -> l
                              Just x' -> Bin sx kx x' l Tip
    go' (NonEmptyDMap _ kx x l r)    = Bin' $! balanceE kx x l (go r)

{--------------------------------------------------------------------
  Union Worker Builders
--------------------------------------------------------------------}

makeUnion
  :: GCompare k
  => ( DMap k f -> DMap k f -> DMap k f
     , NonEmptyDMap k f -> NonEmptyDMap k f -> NonEmptyDMap k f)
makeUnion = (go, go')
  where
    go t1 Tip  = t1
    go t1 (Bin _ kx x Tip Tip) = Bin' $! makeInsertR kx x t1
    go Tip t2  = t2
    go (Bin _ kx x Tip Tip) t2 = Bin' $! makeInsert kx x t2
    go t1@(Bin _ k1 x1 l1 r1) t2 = case fst (makeSplit k1) t2 of
      (l2, r2)
        | l1 `ptrEq` l1l2 && r1 `ptrEq` r1r2 -> t1
        | otherwise -> Bin' $! combineE k1 x1 l1l2 r1r2
        where !l1l2 = l1 `go` l2
              !r1r2 = r1 `go` r2

    go' t1 (NonEmptyDMap _ kx x Tip Tip) = makeInsertR kx x (Bin' t1)
    go' (NonEmptyDMap _ kx x Tip Tip) t2 = makeInsert kx x (Bin' t2)
    go' t1@(NonEmptyDMap _ k1 x1 l1 r1) t2 = case snd (makeSplit k1) t2 of
      (l2, r2)
        | l1 `ptrEq` l1l2 && r1 `ptrEq` r1r2 -> t1
        | otherwise -> combineE k1 x1 l1l2 r1r2
        where !l1l2 = l1 `go` l2
              !r1r2 = r1 `go` r2

makeUnionWithKey
  :: GCompare k
  => (forall v. k v -> f v -> f v -> f v)
  -> ( DMap k f -> DMap k f -> DMap k f
     , NonEmptyDMap k f -> NonEmptyDMap k f -> NonEmptyDMap k f)
makeUnionWithKey f = (go, go')
  where
    go t1 Tip  = t1
    go Tip t2  = t2
    go (Bin _ k1 x1 l1 r1) t2 = case fst (makeSplitLookup k1) t2 of
      (l2, mx2, r2) -> case mx2 of
          Nothing -> Bin' $! combineE k1 x1 l1l2 r1r2
          Just x2 -> Bin' $! combineE k1 (f k1 x1 x2) l1l2 r1r2
        where !l1l2 = go l1 l2
              !r1r2 = go r1 r2

    go' (NonEmptyDMap _ k1 x1 l1 r1) t2 = case snd (makeSplitLookup k1) t2 of
      (l2, mx2, r2) -> case mx2 of
          Nothing -> combineE k1 x1 l1l2 r1r2
          Just x2 -> combineE k1 (f k1 x1 x2) l1l2 r1r2
        where !l1l2 = go l1 l2
              !r1r2 = go r1 r2

{--------------------------------------------------------------------
  Difference Worker Builders
--------------------------------------------------------------------}

makeDifference
  :: GCompare k
  => ( DMap k f -> DMap k g -> DMap k f
     , NonEmptyDMap k f -> NonEmptyDMap k g -> DMap k f
     )
makeDifference = (go, go')
  where
    go Tip _   = Tip
    go t1 Tip  = t1
    go t1 (Bin _ k2 _x2 l2 r2) = case fst (makeSplit k2) t1 of
      (l1, r1)
        | sizeE t1 == sizeE l1l2 + sizeE r1r2 -> t1
        | otherwise -> mergeE l1l2 r1r2
        where
          !l1l2 = l1 `go` l2
          !r1r2 = r1 `go` r2

    go' t1 (NonEmptyDMap _ k2 _x2 l2 r2) = case snd (makeSplit k2) t1 of
      (l1, r1)
        | sizeNE t1 == sizeE l1l2 + sizeE r1r2 -> Bin' t1
        | otherwise -> mergeE l1l2 r1r2
        where
          !l1l2 = l1 `go` l2
          !r1r2 = r1 `go` r2

makeDifferenceWithKey
  :: GCompare k
  => (forall v. k v -> f v -> g v -> Maybe (f v))
  -> ( DMap k f -> DMap k g -> DMap k f
     , NonEmptyDMap k f -> NonEmptyDMap k g -> DMap k f
     )
makeDifferenceWithKey f = (go, go')
  where
    go Tip _   = Tip
    go t1 Tip  = t1
    go (Bin _ k1 x1 l1 r1) t2 = case fst (makeSplitLookup k1) t2 of
      (l2, mx2, r2) -> case mx2 of
          Nothing -> Bin' $! combineE k1 x1 l1l2 r1r2
          Just x2 -> case f k1 x1 x2 of
            Nothing -> mergeE l1l2 r1r2
            Just x1x2 -> Bin' $! combineE k1 x1x2 l1l2 r1r2
        where !l1l2 = go l1 l2
              !r1r2 = go r1 r2

    go' (NonEmptyDMap _ k1 x1 l1 r1) t2 = case snd (makeSplitLookup k1) t2 of
      (l2, mx2, r2) -> case mx2 of
          Nothing -> Bin' $! combineE k1 x1 l1l2 r1r2
          Just x2 -> case f k1 x1 x2 of
            Nothing -> mergeE l1l2 r1r2
            Just x1x2 -> Bin' $! combineE k1 x1x2 l1l2 r1r2
        where !l1l2 = go l1 l2
              !r1r2 = go r1 r2

{--------------------------------------------------------------------
  Intersection Worker Builders
--------------------------------------------------------------------}

makeIntersection
  :: GCompare k
  => ( DMap k f -> DMap k f -> DMap k f
     , NonEmptyDMap k f -> NonEmptyDMap k f -> DMap k f
     )
makeIntersection = (go, go')
  where
    go Tip _ = Tip
    go _ Tip = Tip
    go t1@(Bin s1 k1 x1 l1 r1) t2 =
      let !(l2, found, r2) = fst (makeSplitMember k1) t2
          !l1l2 = go l1 l2
          !r1r2 = go r1 r2
      in if found
         then if l1l2 `ptrEq` l1 && r1r2 `ptrEq` r1
              then t1
              else Bin' $! combineE k1 x1 l1l2 r1r2
         else mergeE l1l2 r1r2

    go' t1@(NonEmptyDMap s1 k1 x1 l1 r1) t2 =
      let !(l2, found, r2) = snd (makeSplitMember k1) t2
          !l1l2 = go l1 l2
          !r1r2 = go r1 r2
      in if found
         then if l1l2 `ptrEq` l1 && r1r2 `ptrEq` r1
              then Bin' t1
              else Bin' $! combineE k1 x1 l1l2 r1r2
         else mergeE l1l2 r1r2

makeIntersectionWithKey
  :: forall k f g h
  .  GCompare k
  => (forall v. k v -> f v -> g v -> h v)
  -> ( DMap k f -> DMap k g -> DMap k h
     , NonEmptyDMap k f -> NonEmptyDMap k g -> DMap k h
     )
makeIntersectionWithKey f = (go, go')
  where
    go :: DMap k f -> DMap k g -> DMap k h
    go Tip _ = Tip
    go _ Tip = Tip
    go (Bin s1 k1 x1 l1 r1) t2 =
      let !(l2, found, r2) = fst (makeSplitLookup k1) t2
          !l1l2 = go l1 l2
          !r1r2 = go r1 r2
      in case found of
           Nothing -> mergeE l1l2 r1r2
           Just x2 -> Bin' $! combineE k1 (f k1 x1 x2) l1l2 r1r2

    go' :: NonEmptyDMap k f -> NonEmptyDMap k g -> DMap k h
    go' (NonEmptyDMap s1 k1 x1 l1 r1) t2 =
      let !(l2, found, r2) = snd (makeSplitLookup k1) t2
          !l1l2 = go l1 l2
          !r1r2 = go r1 r2
      in case found of
           Nothing -> mergeE l1l2 r1r2
           Just x2 -> Bin' $! combineE k1 (f k1 x1 x2) l1l2 r1r2

{--------------------------------------------------------------------
  Submap Worker Builders
--------------------------------------------------------------------}

makeSubmap'
  :: GCompare k
  => (forall v. k v -> k v -> f v -> g v -> Bool)
  -> ( DMap k f -> DMap k g -> Bool
     , NonEmptyDMap k f -> NonEmptyDMap k g -> Bool
     )
makeSubmap' f = (go, go')
  where
    go Tip _ = True
    go _ Tip = False
    go (Bin _ kx x l r) t
      = case found of
          Nothing -> False
          Just (ky, y)  -> f kx ky x y && go l lt && go r gt
      where
        (lt, found, gt) = fst (makeSplitLookupWithKey kx) t

    go' (NonEmptyDMap _ kx x l r) t
      = case found of
          Nothing -> False
          Just (ky, y)  -> f kx ky x y && go l lt && go r gt
      where
        (lt, found, gt) = snd (makeSplitLookupWithKey kx) t

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}

makeFilterWithKey
  :: GCompare k
  => (forall v. k v -> f v -> Bool)
  -> DMap k f -> DMap k f
makeFilterWithKey p = go
  where
    go Tip = Tip
    go t@(Bin _ kx x l r)
      | p kx x    = if l' `ptrEq` l && r' `ptrEq` r
                    then t
                    else Bin' $! combineE kx x l' r'
      | otherwise = mergeE l' r'
      where !l' = go l
            !r' = go r

makePartitionWithKey
  :: forall k f g h
  .  GCompare k
  => (forall v. k v -> f v -> Bool)
  -> DMap k f
  -> (DMap k f, DMap k f)
makePartitionWithKey p m0 = toPair (go m0)
  where
    go :: DMap k f -> (DMap k f :*: DMap k f)
    go Tip = (Tip :*: Tip)
    go (Bin _ kx x l r)
      | p kx x    = ((Bin' $! combineE kx x l1 r1) :*: mergeE l2 r2)
      | otherwise = (mergeE l1 r1 :*: (Bin' $! combineE kx x l2 r2))
      where
        (l1 :*: l2) = go l
        (r1 :*: r2) = go r

makeMapMaybeWithKey
  :: GCompare k
  => (forall v. k v -> f v -> Maybe (g v))
  -> DMap k f
  -> DMap k g
makeMapMaybeWithKey f = go
  where
    go Tip = Tip
    go (Bin _ kx x l r) = case f kx x of
        Just y  -> Bin' $! combineE kx y (go l) (go r)
        Nothing -> mergeE (go l) (go r)

makeMapEitherWithKey
  :: forall k f g h
  .  GCompare k
  => (forall v. k v -> f v -> Either (g v) (h v))
  -> DMap k f
  -> (DMap k g, DMap k h)
makeMapEitherWithKey f = toPair . go
  where
    go :: GCompare k
       => DMap k f -> (DMap k g :*: DMap k h)
    go Tip = (Tip :*: Tip)
    go (Bin _ kx x l r) = case f kx x of
      Left y  -> ((Bin' $! combineE kx y l1 r1) :*: mergeE l2 r2)
      Right z -> (mergeE l1 r1 :*: (Bin' $! combineE kx z l2 r2))
      where
        (l1 :*: l2) = go l
        (r1 :*: r2) = go r

{--------------------------------------------------------------------
  Mapping Worker Builders
--------------------------------------------------------------------}

makeMap
  :: (forall v. f v -> g v)
  -> ( DMap k f -> DMap k g
     , NonEmptyDMap k f -> NonEmptyDMap k g
     )
makeMap f = (go, go')
  where
    go Tip = Tip
    go (Bin' ne) = Bin' $! go' ne

    go' (NonEmptyDMap sx kx x l r) = NonEmptyDMap sx kx (f x) (go l) (go r)

makeMapWithKey
  :: (forall v. k v -> f v -> g v)
  -> ( DMap k f -> DMap k g
     , NonEmptyDMap k f -> NonEmptyDMap k g
     )
makeMapWithKey f = (go, go')
  where
    go Tip = Tip
    go (Bin' ne) = Bin' $! go' ne

    go' (NonEmptyDMap sx kx x l r) = NonEmptyDMap sx kx (f kx x) (go l) (go r)

makeTraverseWithKey
  :: Applicative t
  => (forall v. k v -> f v -> t (g v))
  -> ( DMap k f -> t (DMap k g)
     , NonEmptyDMap k f -> t (NonEmptyDMap k g)
     )
makeTraverseWithKey f = (go, go')
  where
    go Tip = pure Tip
    go (Bin' ne) = Bin' <$> go' ne

    go' (NonEmptyDMap 1 k v _ _) = (\v' -> NonEmptyDMap 1 k v' Tip Tip) <$> f k v
    go' (NonEmptyDMap s k v l r) = flip (NonEmptyDMap s k) <$> go l <*> f k v <*> go r

makeMapAccumLWithKey
  :: (forall v. a -> k v -> f v -> (a, g v))
  -> ( a -> DMap k f -> (a, DMap k g)
     , a -> NonEmptyDMap k f -> (a, NonEmptyDMap k g)
     )
makeMapAccumLWithKey f = (go, go')
  where
    go a Tip       = (a,Tip)
    go a (Bin' ne) = Bin' <$> go' a ne

    go' a (NonEmptyDMap sx kx x l r) =
                 let (a1,l') = go a l
                     (a2,x') = f a1 kx x
                     (a3,r') = go a2 r
                 in (a3, NonEmptyDMap sx kx x' l' r')

makeMapAccumRWithKey
  :: (forall v. a -> k v -> f v -> (a, g v))
  -> ( a -> DMap k f -> (a, DMap k g)
     , a -> NonEmptyDMap k f -> (a, NonEmptyDMap k g)
     )
makeMapAccumRWithKey f = (go, go')
  where
    go a Tip = (a,Tip)
    go a (Bin' ne) = Bin' <$> go' a ne

    go' a (NonEmptyDMap sx kx x l r) =
                 let (a1,r') = go a r
                     (a2,x') = f a1 kx x
                     (a3,l') = go a2 l
                 in (a3, NonEmptyDMap sx kx x' l' r')

makeMapKeysMonotonic
  :: (forall v. k1 v -> k2 v)
  -> ( DMap k1 f -> DMap k2 f
     , NonEmptyDMap k1 f -> NonEmptyDMap k2 f
     )
makeMapKeysMonotonic f = (go, go')
  where
    go Tip = Tip
    go (Bin' ne) = Bin' $! go' ne

    go' (NonEmptyDMap sz k x l r) = NonEmptyDMap sz (f k) x (go l) (go r)

{--------------------------------------------------------------------
  Folds
--------------------------------------------------------------------}

makeFoldrWithKey
  :: (forall v. k v -> f v -> b -> b)
  -> b
  -> DMap k f
  -> b
makeFoldrWithKey f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = go (f kx x (go z r)) l

makeFoldr1WithKey
  :: (forall v. k v -> f v -> b -> b)
  -> (forall v. k v -> f v -> b)
  -> NonEmptyDMap k f -> b
makeFoldr1WithKey f g = go
  where
    go (NonEmptyDMap _ kx x l Tip) = makeFoldrWithKey f (g kx x) l
    go (NonEmptyDMap _ kx x l (Bin' r)) = makeFoldrWithKey f (f kx x (go r)) l

makeFoldlWithKey
  :: (forall v. b -> k v -> f v -> b)
  -> b
  -> DMap k f
  -> b
makeFoldlWithKey f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = go (f (go z l) kx x) r

makeFoldl1WithKey
  :: (forall v. b -> k v -> f v -> b)
  -> (forall v. k v -> f v -> b)
  -> NonEmptyDMap k f -> b
makeFoldl1WithKey f g = go
  where
    go (NonEmptyDMap _ kx x Tip r) = makeFoldlWithKey f (g kx x) r
    go (NonEmptyDMap _ kx x (Bin' l) r) = makeFoldlWithKey f (f (go l) kx x) r

{--------------------------------------------------------------------
  Building trees from ascending/descending lists worker builders
--------------------------------------------------------------------}

makeFromDistinctAscList
  :: ( [DSum k f] -> DMap k f
     , NonEmpty (DSum k f) -> NonEmptyDMap k f
     )
makeFromDistinctAscList
  = ( \xs -> build const (length xs) xs
    , \xs -> build' const (length xs) xs
    )
  where
    -- 1) use continutations so that we use heap space instead of stack space.
    -- 2) special case for n==5 to build bushier trees.

    build
      :: (DMap k f -> [DSum k f] -> b)
      -> Int
      -> [DSum k f]
      -> b
    build c 0 xs'  = c Tip xs'
    build c 5 xs'  = case xs' of
                       ((k1:=>x1):(k2:=>x2):(k3:=>x3):(k4:=>x4):(k5:=>x5):xx)
                            -> c (binE k4 x4 (binE k2 x2 (singletonE k1 x1) (singletonE k3 x3)) (singletonE k5 x5)) xx
                       _ -> error "fromDistinctAscList build"
    build c n xs'  = seq nr $ build (buildR nr c) nl xs'
                   where
                     nl = n `div` 2
                     nr = n - nl - 1

    build'
      :: (NonEmptyDMap k f -> [DSum k f] -> b)
      -> Int
      -> NonEmpty (DSum k f)
      -> b
    build' c 5 xs'  = case xs' of
                       (k1:=>x1) :| ((k2:=>x2):(k3:=>x3):(k4:=>x4):(k5:=>x5):xx)
                            -> c (binNE k4 x4 (binE k2 x2 (singletonE k1 x1) (singletonE k3 x3)) (singletonE k5 x5)) xx
                       _ -> error "fromDistinctAscList build'"
    build' c n xs'  = seq nr $ build' (build'R nr c) nl xs'
                   where
                     nl = n `div` 2
                     nr = n - nl - 1

    -- TODO use 'NonEmpty' to hoist partiality to caller
    buildR
      :: Int
      -> (DMap k f -> [DSum k f] -> b)
      -> DMap k f -> [DSum k f] -> b
    buildR n c l ((k:=>x):ys) = build (buildB l k x c) n ys
    buildR _ _ _ []           = error "fromDistinctAscList buildR []"

    build'R
      :: Int
      -> (NonEmptyDMap k f -> [DSum k f] -> b)
      -> NonEmptyDMap k f -> [DSum k f] -> b
    build'R n c l ((k:=>x):ys) = build (build'B l k x c) n ys
    build'R _ _ _ []           = error "fromDistinctAscList build'R []"

    buildB
      :: DMap k f -> k v -> f v
      -> (DMap k f -> a -> b)
      -> DMap k f -> a -> b
    buildB l k x c r zs = c (binE k x l r) zs

    build'B
      :: NonEmptyDMap k f -> k v -> f v
      -> (NonEmptyDMap k f -> a -> b)
      -> DMap k f -> a -> b
    build'B l k x c r zs = c (binNE k x (Bin' l) r) zs

{--------------------------------------------------------------------
  Split Worker Builders
--------------------------------------------------------------------}

makeSplit
  :: forall k f v. GCompare k
  => k v
  -> ( DMap k f -> (DMap k f, DMap k f)
     , NonEmptyDMap k f -> (DMap k f, DMap k f)
     )
makeSplit k = (toPair . go, toPair . go')
  where
    go :: DMap k f -> (DMap k f :*: DMap k f)
    go Tip       = (Tip :*: Tip)
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> (DMap k f :*: DMap k f)
    go' (NonEmptyDMap _ kx x l r) = case gcompare k kx of
          GLT -> let !(lt :*: gt) = go l in (lt :*: (Bin' $! combineE kx x gt r))
          GGT -> let !(lt :*: gt) = go r in ((Bin' $! combineE kx x l lt) :*: gt)
          GEQ -> (l :*: r)
{-# INLINABLE makeSplit #-}

makeSplitLookup
  :: forall k f v
  .  GCompare k
  => k v
  -> ( DMap k f -> (DMap k f, Maybe (f v), DMap k f)
     , NonEmptyDMap k f -> (DMap k f, Maybe (f v), DMap k f)
     )
makeSplitLookup k = (toTriple . go, toTriple . go')
  where
    go :: DMap k f -> Triple' (DMap k f) (Maybe (f v)) (DMap k f)
    go Tip       = Triple' Tip Nothing Tip
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> Triple' (DMap k f) (Maybe (f v)) (DMap k f)
    go' (NonEmptyDMap _ kx x l r) = case gcompare k kx of
      GLT -> let !(Triple' lt z gt) = go l in Triple' lt z (Bin' $! combineE kx x gt r)
      GGT -> let !(Triple' lt z gt) = go r in Triple' (Bin' $! combineE kx x l lt) z gt
      GEQ -> Triple' l (Just x) r

makeSplitMember
  :: forall k f v
  .  GCompare k
  => k v
  -> ( DMap k f -> (DMap k f, Bool, DMap k f)
     , NonEmptyDMap k f -> (DMap k f, Bool, DMap k f)
     )
makeSplitMember k = (toTriple . go, toTriple . go')
  where
    go :: DMap k f -> Triple' (DMap k f) Bool (DMap k f)
    go Tip       = Triple' Tip False Tip
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> Triple' (DMap k f) Bool (DMap k f)
    go' (NonEmptyDMap _ kx x l r) = case gcompare k kx of
      GLT -> let !(Triple' lt z gt) = go l in Triple' lt z (Bin' $! combineE kx x gt r)
      GGT -> let !(Triple' lt z gt) = go r in Triple' (Bin' $! combineE kx x l lt) z gt
      GEQ -> Triple' l True r

makeSplitLookupWithKey
  :: forall k f v
  .  GCompare k
  => k v
  -> ( DMap k f -> (DMap k f, Maybe (k v, f v), DMap k f)
     , NonEmptyDMap k f -> (DMap k f, Maybe (k v, f v), DMap k f)
     )
makeSplitLookupWithKey k = (toTriple . go, toTriple . go')
  where
    go :: DMap k f -> Triple' (DMap k f) (Maybe (k v, f v)) (DMap k f)
    go Tip       = Triple' Tip Nothing Tip
    go (Bin' ne) = go' ne

    go' :: NonEmptyDMap k f -> Triple' (DMap k f) (Maybe (k v, f v)) (DMap k f)
    go' (NonEmptyDMap _ kx x l r) = case gcompare k kx of
      GLT -> let !(Triple' lt z gt) = go l in Triple' lt z (Bin' $! combineE kx x gt r)
      GGT -> let !(Triple' lt z gt) = go r in Triple' (Bin' $! combineE kx x l lt) z gt
      GEQ -> Triple' l (Just (kx, x)) r

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}

makeShowsTree
  :: (forall v. k v -> f v -> String)
  -> Bool
  -> ( [String] -> [String] -> DMap k f -> ShowS
     , [String] -> [String] -> NonEmptyDMap k f -> ShowS
     )
makeShowsTree showelem wide = (go, go')
  where
    go lbars rbars t = case t of
        Tip -> showsBars lbars . showString "|\n"
        Bin' ne -> go' lbars rbars ne

    go' lbars rbars t = case t of
        NonEmptyDMap _ kx x Tip Tip
            -> showsBars lbars . showString (showelem kx x) . showString "\n"
        NonEmptyDMap _ kx x l r
            -> go (withBar rbars) (withEmpty rbars) r .
               showWide wide rbars .
               showsBars lbars . showString (showelem kx x) . showString "\n" .
               showWide wide lbars .
               go (withEmpty lbars) (withBar lbars) l

makeShowsTreeHang
  :: (forall v. k v -> f v -> String)
  -> Bool
  -> ( [String] -> DMap k f -> ShowS
     , [String] -> NonEmptyDMap k f -> ShowS
     )
makeShowsTreeHang showelem wide = (go, go')
  where
    go bars t = case t of
        Tip -> showsBars bars . showString "|\n"
        Bin' ne -> go' bars ne

    go' bars t = case t of
        NonEmptyDMap _ kx x Tip Tip
            -> showsBars bars . showString (showelem kx x) . showString "\n"
        NonEmptyDMap _ kx x l r
            -> showsBars bars . showString (showelem kx x) . showString "\n" .
               showWide wide bars .
               go (withBar bars) l .
               showWide wide bars .
               go (withEmpty bars) r

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

makeOrdered
  :: forall k f
  .  GCompare k
  => ( DMap k f -> Bool
     , NonEmptyDMap k f -> Bool
     )
makeOrdered
  = ( bounded (const True) (const True)
    , bounded' (const True) (const True)
    )
  where
    bounded
      :: (Some k -> Bool)
      -> (Some k -> Bool)
      -> DMap k f-> Bool
    bounded lo hi t' = case t' of
        Tip     -> True
        Bin' ne -> bounded' lo hi ne

    bounded'
      :: (Some k -> Bool)
      -> (Some k -> Bool)
      -> NonEmptyDMap k f-> Bool
    bounded' lo hi t'
      = case t' of
          NonEmptyDMap _ kx _ l r  -> (lo (This kx)) && (hi (This kx)) && bounded lo (< This kx) l && bounded (> This kx) hi r

-- | Exported only for "Debug.QuickCheck"
makeBalanced
  :: ( DMap k f -> Bool
     , NonEmptyDMap k f -> Bool
     )
makeBalanced = (go, go')
  where
    go t = case t of
        Tip     -> True
        Bin' ne -> go' ne

    go' t = case t of
        NonEmptyDMap _ _ _ l r  -> (sizeE l + sizeE r <= 1 || (sizeE l <= delta*sizeE r && sizeE r <= delta*sizeE l)) &&
                        go l && go r

makeValidsize
  :: ( DMap k f -> Bool
     , NonEmptyDMap k f -> Bool
     )
makeValidsize =
  ( \t -> realsize t == Just (sizeE t)
  , \t -> realsize' t == Just (sizeNE t)
  )
  where
    realsize t = case t of
        Tip -> Just 0
        Bin' ne -> realsize' ne
    realsize' t = case t of
        NonEmptyDMap sz _ _ l r -> case (realsize l,realsize r) of
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

foldl1Strict
  :: (a -> a -> a)
  -> NonEmpty a -> a
foldl1Strict f (x NEL.:| xs) = foldlStrict f x xs
