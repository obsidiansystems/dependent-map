{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
module Data.Dependent.Map.Typeable where

import Data.Dependent.Map.Internal
import Data.Typeable

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702

instance Typeable1 f => Typeable (DMap f) where
    typeOf ds = mkTyConApp dMapCon [typeOfT]
        where
            dMapCon = mkTyCon3 "dependent-map" "Data.Dependent.Map" "DMap"
            typeOfT = typeOf1 $ (undefined :: DMap f -> f a) ds

#else

instance Typeable1 f => Typeable (DMap f) where
    typeOf ds = mkTyConApp dMapCon [typeOfT]
        where
            dMapCon = mkTyCon "Data.Dependent.Map.DMap"
            typeOfT = typeOf1 $ (undefined :: DMap f -> f a) ds

#endif