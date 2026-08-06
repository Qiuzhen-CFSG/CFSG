# Formalization of the Classification of Finite Simple Groups

Work in progress.

## Finished Theorems

### (a) The Odd Order Theorem (Feit–Thompson)

Every finite group of odd order is solvable.

### (b) Suzuki's Theorem on Split BN-Pairs of Rank 1

Suzuki's theorem gives a complete classification of finite groups with a split
BN-pair of rank 1.

## Auditable statements

Each finished theorem is also stated in `comparator/`, over Mathlib and nothing
else, so that no declaration of this repository sits in the trusted base.  A
directory per result holds `Defs.lean`, `Challenge.lean` and `Solution.lean`
together with its `config.json`; the challenge states the theorem, the solution
discharges it from the development, so a weakened transcription fails rather than
passes silently.

| result | directory |
|---|---|
| Bender--Suzuki | `comparator/BenderSuzukiTheorem/` |
| Bender--Suzuki, converse direction | `comparator/BenderSuzukiConverse/` |
| Glauberman's ZJ theorem | `comparator/GlaubermanZJ/` |

CI builds all three.

