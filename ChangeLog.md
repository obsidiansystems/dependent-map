# Revision history for dependent-map

## Unreleased (0.4.1.0)

* Now depends on `monoid-subclasses`.
* New instances `monoid-subclasses`:
  - `instance GCompare k => Factorial (DMap k f)`
  - `instance GCompare k => FactorialMonoid (DMap k f)`
  - `instance GCompare k => OverlappingGCDMonoid (DMap k f)`
  - `instance GCompare k => PositiveMonoid (DMap k f)`
  - `instance GCompare k => MonoidNull (DMap k f)`
  - `instance (GCompare k, Has' Eq k f) => LeftReductive (DMap k f)`
  - `instance (GCompare k, Has' Eq k f) => RightReductive (DMap k f)`
* Provide `foldlWithKey'`.
* Minimum `base` version is now `4.11` (GHC 8.4.x).
* Use canonical `mappend`/`(<>)` definitions.

## 0.4.0.0 - 2020-03-26

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
