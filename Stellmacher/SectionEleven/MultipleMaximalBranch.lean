module
public import Stellmacher.SectionEleven.MultipleMaximalHypothesisTwo
public import Stellmacher.SectionEleven.MultipleEightTwoTerminal
public import Stellmacher.SectionEleven.MultipleEightSixClassification
public import Stellmacher.SectionEleven.MultipleNineDistanceThree
public import Stellmacher.SectionEleven.MultipleTenOneRealization
public import Stellmacher.SectionTen.AmbientTenOne

/-!
# The multiple-maximal branch of the generalized N-group classification

Suppose every ambient two-local is solvable of characteristic two and two
distinct maximal two-locals contain the supplied Sylow subgroup. Then H has
one of the four exceptional local types. All global hypotheses stay on H;
the generated graph lives on the join selected by the native setup theorem.

For noncommuting critical centers, the noncentral (8.2) classification or
the central (8.6) classification supplies the exceptional type; actual
nonsolvable two-local alternatives are excluded by the ambient hypothesis.
For commuting centers, the proved (9.10) and distance-one exclusion give
length three. The actual (10.1) alternative supplies its type data or an
ambient nonsolvable involution centralizer, which the local hypothesis excludes.

Source: Stellmacher, Section Eleven, printed66–67. This is the direct N2
branch and uses no unproved Theorem One declaration.
-/

namespace Stellmacher.SectionEleven
open Later SectionsFiveToSeven SectionNine
universe u


private theorem ten_one_terminal_classification
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a,ctx.Γ.z ctx.criticalPath.a'⁆=⊥)
    (hlength : ctx.criticalPath.length=3) :
    (∃ next : ctx.Γ.Vertex, ∃ W W0 Wnext : Subgroup (P1 ⊔ P2 : Subgroup H),
      TenOneCaseBTypeData ctx.Γ ctx.criticalPath next W W0 Wnext) ∨
    (∃ element : (P1 ⊔ P2 : Subgroup H), Later.IsInvolution element ∧
      ¬ Group.IsSolvable (Subgroup.centralizer ({(element : H)} : Set H))) := by
  let tenCtx := (ctx.toSectionNineContext hcomm).toTenContext hlength
  let middle := ctx.criticalPath.path ⟨2,by omega⟩
  have hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle :=
    ⟨⟨2,by omega⟩,rfl,rfl⟩
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
  let Wnext := GeneratedNeighborhoodV ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext
  exact SectionTen.ambient_ten_one_case_b_or_nonsolvable_centralizer_of_conclusion
    tenCtx middle W W0 Wnext hpath
    (SectionTen.ambient_lemma_ten_one tenCtx middle W W0 Wnext hpath rfl rfl rfl)

private theorem terminal_classification
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    : IsOfExceptionalType H := by
  by_cases hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥
  · have hlength : ctx.criticalPath.length = 3 :=
      multiple_nine_distance_three ctx hLocal hcomm
    exact Or.inr (Or.inr (Or.inr
      (multiple_ten_one_of_terminal_alternative ctx hLocal (ten_one_terminal_classification ctx hcomm hlength))))
  · by_cases hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
        CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)
    · exact Or.inr (Or.inr (Or.inl
        (multiple_eight_six_of_classification ctx hLocal (multiple_eight_six_classification ctx hcomm hcenter))))
    · rcases multiple_eight_two_terminal ctx hcomm hcenter with hL3 | hSp4
      · exact Or.inl hL3
      · exact Or.inr (Or.inl hSp4)

public theorem multiple_maximal_branch
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (hHyp : HypothesisOne H S0)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ M1 M2 : Subgroup H, M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧
      IsMaximalTwoLocal M2 ∧ (S0 : Subgroup H) ≤ M1 ∧ (S0 : Subgroup H) ≤ M2)
    : IsOfExceptionalType H := by
  obtain ⟨P1, P2, ⟨ctx⟩⟩ := multiple_maximal_terminal_context S0 hHyp hLocal hmax
  exact terminal_classification ctx hLocal

end Stellmacher.SectionEleven
