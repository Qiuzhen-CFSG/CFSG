module

public import Stellmacher.SectionEleven.MultipleMaximalBranch

/-!
# The large terminal context retained by the multiple-maximal reduction

The original Section Eleven inputs give one of the local L3(2), Sp4(2),
or G2(2)' types, or an actual Sylow terminal context with commuting critical
endpoints, critical length three, and no quotient transvections. The last
alternative retains the ambient Hypothesis Two and the native subgroup that
is the restriction of the supplied ambient Sylow. Its Section Ten adapter
therefore exposes the proved large-case geometry without replacing it by a
local type that forgets these data.

The selected context and the noncommuting alternatives are the same as in
`multiple_maximal_branch`. In the commuting case, the distance theorem gives
length three. A quotient transvection would force the small Section Ten
configuration and its actual nonsolvable ambient involution centralizer,
contradicting the solvability of every ambient two-local. Thus the absence
of transvections is proved from the existing hypotheses.

This companion preserves the original local-classification endpoints. It
supplies the richer input for the subsequent Tits involution-centralizer
analysis; full centralizer equality and Parrott recognition are not claimed
here. Source: Stellmacher, Section Eleven and (10.1), printed pp.59--67 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven SectionNine

universe u

private theorem no_quotient_transvections
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥)
    (hlength : ctx.criticalPath.length = 3)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U) :
    ∀ actor : (P1 ⊔ P2 : Subgroup H), actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2 := by
  intro actor hactor hout hindex
  let tenCtx := ctx.toSectionTenContext hcomm hlength
  let middle := ctx.criticalPath.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  obtain ⟨hsmall, hmodel⟩ :=
    SectionTen.ten_one_transvection_small_first tenCtx middle hpath actor hactor hout hindex
  obtain ⟨point, hpoint, _, _, hbad⟩ :=
    SectionTen.ten_one_small_nonsolvable_centralizer tenCtx middle hpath hsmall hmodel
  exact hbad (ten_one_ambient_involution_centralizer_solvable
    (P1 ⊔ P2).subtype (P1 ⊔ P2).subtype_injective hLocal point hpoint)

/-- The multiple-maximal case retains its actual large Section Ten context. -/
public theorem multiple_maximal_rich_terminal
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (hHyp : HypothesisOne H S0)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ M1 M2 : Subgroup H, M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧
      IsMaximalTwoLocal M2 ∧ (S0 : Subgroup H) ≤ M1 ∧ (S0 : Subgroup H) ≤ M2) :
    IsOfL3TwoType H ∨ IsOfSp4TwoType H ∨ IsOfGTwoTwoDerivedType H ∨
      ∃ P1 P2 : Subgroup H, ∃ ctx : SylowTerminalContext H S0 P1 P2,
        ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥ ∧
        ctx.criticalPath.length = 3 ∧
        ∀ actor : (P1 ⊔ P2 : Subgroup H), actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
          actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
            (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
              ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2 := by
  obtain ⟨P1, P2, ⟨ctx⟩⟩ := multiple_maximal_terminal_context S0 hHyp hLocal hmax
  by_cases hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥
  · have hlength := multiple_nine_distance_three ctx hLocal hcomm
    exact Or.inr (Or.inr (Or.inr
      ⟨P1, P2, ctx, hcomm, hlength, no_quotient_transvections ctx hcomm hlength hLocal⟩))
  · by_cases hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
        CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)
    · exact Or.inr (Or.inr (Or.inl
        (multiple_eight_six_of_classification ctx hLocal
          (multiple_eight_six_classification ctx hcomm hcenter))))
    · rcases multiple_eight_two_terminal ctx hcomm hcenter with hL3 | hSp4
      · exact Or.inl hL3
      · exact Or.inr (Or.inl hSp4)

end Stellmacher.SectionEleven
