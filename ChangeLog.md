# Revision history for dependent-map

## Unreleased

* Stop re-exporting `Some(..)`, `GCompare(..)`, and `GOrdering(..)` from `dependent-sum` (which itself re-exports from `some` in some versions).
* Stop re-exporting `DSum(..)` from `dependent-sum`.

## 0.3.1.0 - 2020-03-26

* Drop support for non-GHC compilers.
* Drop support for GHC < 8.
* Update maintainer and GitHub links.
* Support `dependent-sum` 0.7.
* Add `ffor`, `fforWithKey`, `forWithKey`, `forWithKey_`, and `traverseWithKey_` to `Data.Dependent.Map`.
* Enable `PolyKinds` for `Data.Dependent.Map.Lens`.

## 0.3 - 2019-03-21

* Change instances of Eq, Ord, Read, Show to use Has' from constraints-extras instead of *Tag classes.
* This ends support for GHC 7.x.
