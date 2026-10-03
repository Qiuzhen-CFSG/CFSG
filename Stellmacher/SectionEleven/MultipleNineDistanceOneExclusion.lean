module

public import Stellmacher.SectionEleven.MultipleNineDistanceReduction
public import Stellmacher.SectionNine.DistanceOneFaithfulProducer
public import Stellmacher.SectionNine.DistanceOneCoreEquality

/-!
# Excluding critical distance one in the Sylow terminal branch

When every ambient two-local subgroup is solvable of characteristic-two type,
a commuting Sylow terminal critical pair cannot have distance one. The proved
faithful-action and core-equality producers supply the local structure of (9.1).
Its actual ambient elementary-eight normalizer then has a nonsolvable PSL₃(2)
quotient, contradicting the ambient solvability hypothesis.

The graph remains on the generated join and Hypothesis Two remains on the
original group. This discharges the distance-one inputs of the Section Eleven
reduction; combining it with the still-separate (9.10) bound and oddness gives
critical length three.

Source: Stellmacher (9.1)(c) and the Section Eleven deduction of Theorem 2,
`refs/files/stellmacher-n-group.pdf` and `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven SectionNine

universe u

public theorem multiple_nine_distance_ne_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥) :
    ctx.criticalPath.length ≠ 1 := by
  apply multiple_nine_distance_ne_one_of_local_data ctx hLocal hcomm
  · exact fun hlength => distance_one_faithful_conclusion
      (ctx.toSectionNineContext hcomm) hlength
  · intro hlength
    exact distance_one_core_eq_center_of_faithful
      (ctx.toSectionNineContext hcomm) hlength
      (distance_one_faithful_conclusion (ctx.toSectionNineContext hcomm) hlength)

end Stellmacher.SectionEleven
