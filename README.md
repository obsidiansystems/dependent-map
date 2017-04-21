dependent-map [![Build Status](https://travis-ci.org/mokus0/dependent-map.svg)](https://travis-ci.org/mokus0/dependent-map)
==============

This library defines a dependently-typed finite map type.  It is derived from Data.Map.Map in the containers package, but rather than (conceptually) storing pairs indexed by the first component, it stores `DSum`s (from the `dependent-sum` package) indexed by tag.  For example (using the types from the `dependent-sum` package's `FooGADT` example):


    {-# LANGUAGE GADTs #-}
    import FooGADT
    import Data.Dependent.Map
    import Data.Functor.Identity

    x = fromList [Foo :=> Identity pi, Baz :=> Identity "hello there"]
    y = singleton Bar (Identity 43)
    z = union y (read "fromList [Foo :=> Identity (-1.1415926535897931)]")

    addFoo :: (Applicative f) => Foo v -> f v -> f v -> f v
    addFoo Foo fx fy = (+) <$> fx <*> fy
    addFoo _   fx _ = fx

    main = mapM_ print
        [ x, y, z
        , unionWithKey addFoo x z
        ]

Which prints:

    fromList [Foo :=> Identity 3.141592653589793,Baz :=> Identity "hello there"]
    fromList [Bar :=> Identity 43]
    fromList [Foo :=> Identity (-1.1415926535897931),Bar :=> Identity 43]
    fromList [Foo :=> Identity 2.0,Bar :=> Identity 43,Baz :=> Identity "hello there"]
