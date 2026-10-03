module

public import Stellmacher.SectionEleven.SylowTerminalContext
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionNine.DistanceOneLocalStructure
public import Stellmacher.SectionNine.DistanceOneNormalizerConstruction

/-!
# Reductions for the commuting Sylow critical distance

The proved (7.5) supplies odd critical distance. The ambient normalizer witness
in (9.1)(c) is incompatible with solvability of every ambient two-local: its
elementary subgroup of order eight is nontrivial, and its actual normalizer
has the nonsolvable PSL₃(2) quotient. The graph remains in the generated join;
the normalizer and the solvability hypothesis both remain in H.

The distance-one reduction explicitly requires the faithful-action and initial
core-equality producers. The arithmetic reduction explicitly requires the
distance bound from (9.10). These conditional helpers do not assert the final
distance-three theorem before those upstream results have been proved.

Source: Stellmacher, (7.5), (9.1)(c), and (9.10),
`refs/files/stellmacher-n-group.pdf`. The abbreviated LaTeX transcription of
(9.1) has incorrect local orders and model notation; the existing faithful
and local conclusion predicates use the scan-correct order and wreath model.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven SectionNine

universe u

public theorem multiple_nine_distance_odd
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥) :
    Odd ctx.criticalPath.length :=
  (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath hcomm).odd_distance

public theorem multiple_nine_normalizer_input_impossible
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥)
    (hwitness : DistanceOneNormalizerInput (P1 ⊔ P2).subtype
      (ctx.toSectionNineContext hcomm).toLocalContext) : False := by
  obtain ⟨U, _, helementary, hcard, hcentral, X, Y, hne, hX, hY⟩ := hwitness
  let _ : IsElementaryAbelian 2 U := helementary
  have hUne : U ≠ ⊥ := by
    intro hbot
    simp only [hbot, Subgroup.card_bot] at hcard
    omega
  have htwoLocal : IsTwoLocal (Subgroup.normalizer (U : Set H)) :=
    ⟨U, hUne, IsElementaryAbelian.isPGroup 2 U, rfl⟩
  let _ := (hLocal _ htwoLocal).1
  obtain ⟨equiv⟩ :=
    elementaryEight_normalizer_quotient_equiv_PSL3 U hcard hcentral X Y hne hX hY
  exact not_isSolvable_psl3_two
    (Group.isSolvable_of_surjective (f := equiv.toMonoidHom) equiv.surjective)

public theorem multiple_nine_distance_ne_one_of_local_data
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥)
    (hfaith : ctx.criticalPath.length = 1 → DistanceOneFaithfulConclusion
      (ctx.toSectionNineContext hcomm).toLocalContext)
    (hcore : ctx.criticalPath.length = 1 →
      QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a) :
    ctx.criticalPath.length ≠ 1 := by
  intro hlength
  have hlocal := distance_one_local_conclusion_of_core_eq_center
    (ctx.toSectionNineContext hcomm) hlength (hfaith hlength) (hcore hlength)
  exact multiple_nine_normalizer_input_impossible ctx hLocal hcomm
    (distance_one_normalizer_input_of_local_structure
      (ctx.toSectionNineContext hcomm) hlength (hfaith hlength) hlocal)

public theorem multiple_nine_distance_three_of_bound_and_ne_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥)
    (hbound : ctx.criticalPath.length ≤ 3)
    (hne : ctx.criticalPath.length ≠ 1) :
    ctx.criticalPath.length = 3 := by
  obtain ⟨half, hhalf⟩ := multiple_nine_distance_odd ctx hcomm
  omega

end Stellmacher.SectionEleven
