This file describes changes in the UGALY package.

## 4.1.3 (2023-07-07)

- Add `LocalActionPGL2Qp`, `LocalActionPSL2Qp`,
  `GetPGL2QpPermutationFromMatrix` and `GetP1RepresentativeFromLattice`,
  contributed by Tasman Fell

## 4.0.3 (2022-07-14)

- Adjust manual examples to newer GAP versions (#10, #11)

## 4.0.2 (2022-04-02)

- Add FGA as a needed package, for `SmallGeneratingSet` on subgroups of free
  groups (#6)
- Stop printing the result of `InvolutiveCompatibilityCocycle` in two manual
  examples, as its output differs between GAP versions (#8)

## 4.0.1 (2022-02-07)

- Fix two manual examples

## 4.0 (2021-10-14)

- Rename `GAMMA`, `DELTA`, `PHI`, `PI`, `SIGMA` and `LocalElement` to
  `LocalActionGamma`, `LocalActionDelta`, `LocalActionPhi`, `LocalActionPi`,
  `LocalActionSigma` and `LocalActionElement`, to avoid names that clash with
  others up to case
- Rename `IsDiscrete` to `YieldsDiscreteUniversalGroup`
- Improve the cocycle functions

## 3.0 (2021-07-29)

- Rename `gamma` to `LocalElement`
- Speak of "generalised universal groups" in the manual
- Fix errors in manual examples, and extend the Purpose section

## 2.0.1 (2021-07-14)

- Fix a bug in `CompatibleKernels` caused by changes to `PHI`
- Extend the Purpose section of the manual, and fix manual examples and
  references

## 2.0 (2021-06-04)

- Add the category `IsLocalAction`; many functions are now attributes of local
  actions, including `ConjugacyClassRepsCompatibleSubgroups`
- Rename `AutB` to `AutBall`, `Addresses` to `BallAddresses`,
  `AreCompatibleElements` to `AreCompatibleBallElements` and
  `CompatibleElement` to `CompatibleBallElement`, to avoid name clashes with
  other packages
- Remove `PHI` for arguments `d, F`, which clashed with `PHI` for `l, F`
- Add argument checks, and fix a bug in `AddressOfLeaf`
- Add a Purpose section to the manual

## 1.0 (2020-11-10)

- Initial release
