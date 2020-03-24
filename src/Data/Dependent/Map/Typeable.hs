{-# LANGUAGE Trustworthy #-}
module Data.Dependent.Map.Typeable where

import Data.Dependent.Map.Internal
import Data.Typeable

instance (Typeable1 k, Typeable1 f) => Typeable (DMap k f) where
    typeOf ds = mkTyConApp dMapCon [typeOfK, typeOfF]
        where
            typeOfK = typeOf1 $ (undefined :: DMap k f -> k a) ds
            typeOfF = typeOf1 $ (undefined :: DMap k f -> f a) ds
            dMapCon = mkTyCon3 "dependent-map" "Data.Dependent.Map" "DMap"
