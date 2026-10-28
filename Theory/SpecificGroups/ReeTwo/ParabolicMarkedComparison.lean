module

public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Verified

/-!
# Compatible marked first parabolics for the binary Ree and Tits groups

The verified root-and-Weyl map identifies `ReeTwo.Centralizer` with the actual
first parabolic in `ReeF4.Model 0`. The fixed Atlas embedding identifies the
Tits intersection with the mixed character kernel. Both comparisons preserve
the specified Sylow subgroup, the whole parabolic overlap, the intrinsic
two-core, and the source central involution generating Ω₁(Z(T)).

`Verified` discharges the ambient relation premise using kernel-checked matrix
products and the existing comparison with the actual Chevalley root curves.
Its quotient maps commute with the literal core quotient projections.

Sources: Aschbacher--Smith 14.2.21, printed p.989; Aschbacher (1982), Section 3;
Parrott (1972), pp.672,683; Shinoda (1975), pp.81--83.
-/
