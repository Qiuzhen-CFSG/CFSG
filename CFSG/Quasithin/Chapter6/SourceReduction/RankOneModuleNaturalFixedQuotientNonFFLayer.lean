module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSectionBudget

/-!
# A non-FF constituent contains the original moved module

The cubic budget is supplied by the original source hypotheses. If the
component moved the quotient by a non-FF constituent, the same elementary
actor would be an offender on both sections. This contradicts the chosen
constituent's non-FF property. Hence that actual quotient is centralized
by the component, and all original component displacements lie in the
constituent.

Source: Aschbacher–Smith 5.1.3, the proper-submodule argument, pp.630–631.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

private theorem moved_le_of_quotient_kernel
    {E X : Type*} [Group E] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) E X) (K : Subgroup E) (U : Subrepresentation ρ)
    (hK : K ≤ U.quotientRepresentation.ker) : subspaceCommutator ρ ⊤ K ≤ U.toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, v, _, rfl⟩
  apply (Submodule.Quotient.eq U.toSubmodule).mp
  have he := DFunLike.congr_fun (hK ha) (U.toSubmodule.mkQ v)
  change U.quotientRepresentation a (U.toSubmodule.mkQ v) = U.toSubmodule.mkQ v at he
  rw [U.quotientRepresentation_mk] at he
  exact he

/-- The original full-module bound forces a non-FF invariant section to
contain every component displacement. The elementary actor is selected
from that bound; none is supplied as a premise. -/
theorem Input.moved_le_nonFF_section
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    let J := L ⊔ (T : Subgroup G)
    let V₀ := W.subgroupOf J
    letI := h.reduced_internal.normal
    letI := h.reduced_internal.elementary
    let q := QuotientGroup.mk' (pCore 2 J)
    let hk : q.ker = centralizer (V₀ : Set J) :=
      (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_eq_twoCore.symm
    let ρ := NormalElementaryQuotient.representation V₀ q
      (QuotientGroup.mk'_surjective _) hk
    let K := (L.subgroupOf J).map q
    ∀ U : Subrepresentation ρ, ¬ K ≤ U.toRepresentation.ker →
      ¬ IsFFModule U.toRepresentation →
        K ≤ U.quotientRepresentation.ker ∧ subspaceCommutator ρ ⊤ K ≤ U.toSubmodule := by
  let J := L ⊔ (T : Subgroup G)
  let V₀ := W.subgroupOf J
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let q := QuotientGroup.mk' (pCore 2 J)
  have hk : q.ker = centralizer (V₀ : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_eq_twoCore.symm
  let ρ := NormalElementaryQuotient.representation V₀ q
    (QuotientGroup.mk'_surjective _) hk
  let K := (L.subgroupOf J).map q
  change ∀ U : Subrepresentation ρ, ¬ K ≤ U.toRepresentation.ker →
    ¬ IsFFModule U.toRepresentation → _
  intro U hU hnon
  have hquot : K ≤ U.quotientRepresentation.ker := by
    by_contra hnq
    obtain ⟨A, hA, _, hbudget⟩ := (cubicRatio_le_nat_iff ρ 2).mp
      h.core_quotient_cubicRatio_le_two
    obtain ⟨_, _, _, _, _, _, _, hff, _⟩ :=
      h.original_section_offender_budget U hU hnq A hA hbudget
    exact hnon hff
  exact ⟨hquot, moved_le_of_quotient_kernel ρ K U hquot⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
