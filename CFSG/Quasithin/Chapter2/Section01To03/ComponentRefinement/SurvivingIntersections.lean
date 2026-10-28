module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.SmallLinear
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuShapes
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.MathieuEleven

/-!
# Surviving linear and Mathieu component intersections

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(e,f) and 2.3.9(7)(d–f), printed pp.502 and 525–526.

The genuine local setup supplies a Sylow subgroup of L equal to S ∩ L;
an involution projection of z is central in it. Odd prime cores of L ∩ M
vanish by subnormality in the characteristic-two group H ∩ M. The direct
M₁₁-model intersection is re-exported. The direct M₂₂- and M₂₃-model
intersections are identified with hexad and heptad stabilizers, giving their
actual normal E₁₆ kernels and alternating quotients A₆ and A₇, respectively.
The small prime-field overlaps are accounted for by actual PSL₂(5) ≃ PSL₂(4)
and PSL₂(7) ≃ PSL₃(2) comparisons, with parameters at most three excluded.

The linear overgroup calculations and central-two-cover elimination
remain separate mathematical obligations.
This module does not yet assert all of 2.3.9(7)(d–f).
-/
