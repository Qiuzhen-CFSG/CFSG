module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarOvergroupAction
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarReducedEnlargement

/-!
# Checked Chapter 6 H-star consumer

This is the first direct consumer of the H-star action adapters.  It combines
the source enlargement to `R₂(LT)` with the actual overgroup action on
`X ∈ H(T)`.  The H-star witness, its noncentral omega movement, the inclusion
`H ≤ X`, and the one-or-two A₅ exclusion are all retained as premises.  The
conclusion is the conditional FF/B.5.6 alternative together with the literal
residual-image containment used by the later factor analysis.

Source: Aschbacher--Smith 6.1.5, printed pp.666--668.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H X : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The source-compatible H-star consumer for the enlarged local input and the
literal B.5.6 overgroup action.  No centralizer conclusion is hidden here. -/
theorem checked_hstar_overgroup_consumer
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) (hX : X ∈ Chapter1.HOver G (T : Set G))
    (hnotA5 : ¬ IsOneOrTwoA5Modules L
      (layer L (reducedSubgroup (L ⊔ (T : Subgroup G))))) :
    RankOneGeneric.Input KnownSimple.IsKnownSimple T L
      (reducedSubgroup (L ⊔ (T : Subgroup G))) n ∧
    (let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
     letI := (h.overgroup_omega_orbit_reduced hX).normal
     letI := (h.overgroup_omega_orbit_reduced hX).elementary
     let C := centralizer (U : Set X)
     let q := QuotientGroup.mk' C
     let ρ := NormalElementaryQuotient.representation U q
       (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
     IsFFModule ρ ∧
       ChapterB.SourceInduction.NontrivialAdequateAlternative
         (ρ.comp (offenderSubgroup ρ).subtype) ∧
       (pResidual 2 H).map
         (q.comp (inclusion hHX)) ≤ offenderSubgroup ρ) := by
  refine ⟨h.rankOneInput_of_reduced_enlargement hout hnotA5, ?_⟩
  have hc := h.hstar_overgroup_offender_classification hout hH hZH hHX hX
  have hi := h.hstar_residual_image_le_overgroup_offender hout hH hZH hHX hX
  exact ⟨hc.1, hc.2, hi⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
