module

public import Theory.SpecificGroups.SL2.SubgroupTwoCore
public import Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap.Contracts

/-!
# Rank-one core control for the symplectic plane quotient

The intrinsic two-core theorem for subgroups of the actual SL₂ matrix group
discharges `RankOneCoreControl`. In particular it applies to the range of
`Plane.quotientMap.comp j` used by the plane-local rank-gap argument. No ambient
normality, field-size lower bound, or plane image bound is required.

Source application: Aschbacher–Smith, `refs/quasithin.pdf`, E.1.14(1), printed
p.214, citing Aschbacher [Asc82a], Lemma 4.7. The enclosing symplectic rank-gap
assembly retains the independent plane image calculation.
-/

namespace Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The rank-one core-control input, with all its local premises discharged. -/
public theorem rankOneCoreControl : RankOneCoreControl F :=
  Matrix.SpecialLinearGroup.isPGroup_le_twoCore_of_ne_bot

end Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap
