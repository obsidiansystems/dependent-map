{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
module Data.Dependent.Map.Typeable where

import Data.Dependent.Map.Internal
import Data.Typeable

instance (Typeable1 k, Typeable1 f) => Typeable (DMap k f) where
    typeOf ds = mkTyConApp dMapCon [typeOfK, typeOfF]
        where
            typeOfK = typeOf1 $ (undefined :: DMap k f -> k a) ds
            typeOfF = typeOf1 $ (undefined :: DMap k f -> f a) ds

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
            dMapCon = mkTyCon3 "dependent-map" "Data.Dependent.Map" "DMap"
#else
            dMapCon = mkTyCon "Data.Dependent.Map.DMap"

#endif
