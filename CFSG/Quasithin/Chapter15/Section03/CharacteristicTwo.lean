module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankInequality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.OffenderSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.Terminal

/-!
# Characteristic-two elimination in Section 15.3

Theorems 15.3.13 and 15.3.25 exclude `F*(I) = O₂(I)` for outside
overgroups under Hypothesis 15.3.10. Their two branches have
`m₃(Y₊) = 2` and `m₃(Y₊) = 1`. This module retains their assembly.

The completed terminal ingredients are the paired-module rank inequality
(!) on p.1133, its sharp maximum-elementary replacement, and finite
selection of minimal nontrivial action images. The replacement supplies
the required maximum-order equality. Minimal-image exclusion then yields
the Thompson equality, which is transported from the local action group
to the ambient group. The two relative normality statements and the
earlier uniqueness theorem give the final normalizer contradiction.
The direct factors are normal in `XS`, not necessarily in the ambient group.

`LocalData` fixes the orthogonal coordinates and all local constructions.
`ComponentWitness` and `NaturalEightAction` specify actual outputs for the
remaining construction arguments; neither asserts that these outputs exist.

The characteristic-two exclusion remains unfinished. It requires the
C-components of `J(I)` from 15.3.15/26, the rank-two block eliminations,
the rank-one construction of the `S₈` orthogonal module and its conjugate
in 15.3.27–32, and the paired offender calculation which supplies the
premises of the terminal argument. None is asserted by a record projection
or rank tuple. In using 15.3.12, distinguish its proof's three-part order
`|Y_C|₃ = 3` from the stronger printed `|Y_C| = 3`; the preliminaries
establish an obstruction to that stronger claim under the local hypotheses.
The genuine orthogonal setup and explicit earlier results 15.3.2–12 are
inputs to this conditional local elimination, to be discharged by the
Section 15.3 parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Theorems 15.3.13 and 15.3.25, printed pp.1125–1134 (PDF pp.1142–1151).
-/
