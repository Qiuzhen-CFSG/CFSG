module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion.Alternating
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion.G2
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion.Tits
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion.Triality

/-!
# Small-model exclusions in the initial parabolic selection

The five separate exclusions use the actual component image D = L⁺ and
its local intersection M_I⁺ ∩ D. The full O₂,Φ shadow gives order and
three-rank obstructions; the normal local intersection has a nontrivial
two-core. Concrete subgroup geometry excludes binary triality, the actual
commutators PSp₄(2)′ and G₂(2)′, the Parrott Tits group, and A₆.

The alternating and Tits cases retain the permitted `QuotientParabolic`
hypothesis for strict properness. The G₂ and triality normalizer arguments
follow already from `Setup`. Thus all five apply to the published source
action, without an additional action or recognition premise. The PSL₃(2)
exclusion remains the imported `Setup.not_linear_three_two`.
Combination of the `ExceptionalModel` constructors belongs to the parent
selection assembly, including its independent rank-one exclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.41 and initial parabolic selection, printed pp.1138--1139;
Theorem C and Remark A.2.4, p.33; 1.1.5(3)(a)--(c), pp.501--502.
-/
