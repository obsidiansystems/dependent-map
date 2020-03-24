dependent-map [![Build Status](https://travis-ci.org/obsidiansystems/dependent-map.svg)](https://travis-ci.org/obsidiansystems/dependent-map) [![Hackage](https://img.shields.io/hackage/v/dependent-map.svg)](http://hackage.haskell.org/package/dependent-map)
==============

This library defines a dependently-typed finite map type.  It is derived from Data.Map.Map in the containers package, but rather than (conceptually) storing pairs indexed by the first component, it stores `DSum`s (from the `dependent-sum` package) indexed by tag.  For example (using the types from the `dependent-sum` package's `FooGADT` example):

```haskell
{-# LANGUAGE GADTs #-}
import FooGADT
import Data.Dependent.Map

x = fromList [Foo :=> pi, Baz :=> "hello there"]
y = singleton Bar 42
z = union y (read "fromList [Foo :=> (-1.1415926535897931)]")

addFoo :: Foo v -> v -> v -> v
addFoo Foo x y = x + y
addFoo _   x _ = x

main = mapM_ print
  [ x, y, z
  , unionWithKey addFoo x z
  ]
```

Which prints:

```haskell
fromList [Foo :=> 3.141592653589793,Baz :=> "hello there"]
fromList [Bar :=> 42]
fromList [Foo :=> -1.1415926535897931,Bar :=> 42]
fromList [Foo :=> 2.0,Bar :=> 42,Baz :=> "hello there"]
```

This library can be found on Hackage: https://hackage.haskell.org/package/dependent-map
