dependent-map [![Build Status](https://travis-ci.org/obsidiansystems/dependent-map.svg)](https://travis-ci.org/obsidiansystems/dependent-map) [![Hackage](https://img.shields.io/hackage/v/dependent-map.svg)](http://hackage.haskell.org/package/dependent-map)
==============

This library defines a dependently-typed finite map type. It is derived from `Data.Map.Map` in the `containers` package, but rather than (conceptually) storing pairs indexed by the first component, it stores `DSum`s (from the `dependent-sum` package) indexed by tag. For example

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Example where

import Data.Constraint.Extras.TH (deriveArgDict)
import Data.Dependent.Map (DMap, fromList, singleton, union, unionWithKey)
import Data.Dependent.Sum ((==>))
import Data.Functor.Identity (Identity(..))
import Data.GADT.Compare.TH (deriveGCompare, deriveGEq)
import Data.GADT.Show.TH (deriveGShow)

data Tag a where
  StringKey :: Tag String
  IntKey    :: Tag Int
  DoubleKey :: Tag Double
deriveGEq ''Tag
deriveGCompare ''Tag
deriveGShow ''Tag
deriveArgDict ''Tag

x :: DMap Tag Identity
x = fromList [DoubleKey ==> pi, StringKey ==> "hello there"]

y :: DMap Tag Identity
y = singleton IntKey (Identity 42)

z :: DMap Tag Identity
z = y `union` fromList [DoubleKey ==> -1.1415926535897931]

addFoo :: Tag v -> Identity v -> Identity v -> Identity v
addFoo IntKey (Identity x) (Identity y) = Identity $ x + y
addFoo DoubleKey (Identity x) (Identity y) = Identity $ x + y
addFoo _ x _ = x

main :: IO ()
main = mapM_ print
  [ x, y, z
  , unionWithKey addFoo x z
  ]
```
