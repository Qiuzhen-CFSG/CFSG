module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneImage
/-!
# Central covers preserve the source seed plane and Sylow point

A fixed central kernel cannot meet the transitive three-vector seed orbit.
The quotient point has binary dimension one and is therefore fixed by its
source Sylow group. These statements retain the original quotient action.

Source: Aschbacher–Smith, 13.7.6(i)–(iii), printed p.939.
-/
@[expose] public section
open Subgroup Representation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
open Section08.TransvectionParabolic.Marking.CompatibleFlags
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
/-- A central kernel is disjoint from the original transitive seed plane. -/
theorem seed_cover_injective
    (hL₁H : sourceOne L T V₁ ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (p : Additive (Section08.Source.Utilde H V₃ V₁) →ₗ[ZMod 2] E)
    (hk : ∀ u, p u = 0 → ∀ l : sourceOne L T V₁,
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) u = u) :
    Function.Injective (p.domRestrict (sectionImage H V₃ V₁ V₃)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply _root_.eq_bot_iff.mpr
  intro u hu
  change u = 0
  by_contra hn
  have hun : u.val ≠ 0 := fun hz => hn (Subtype.ext hz)
  have hall : ∀ w ∈ sectionImage H V₃ V₁ V₃, w ≠ 0 → w = u := by
    intro w hw hw0
    obtain ⟨l,hl⟩ := seed_section_nonzero_orbit d hL₁H ρ hρ u u.property hun w hw hw0
    exact hl.symm.trans (hk u hu l)
  have he : sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2) {u.val} := by
    apply le_antisymm
    · intro w hw
      by_cases hz : w = 0
      · exact hz ▸ Submodule.zero_mem _
      · rw [hall w hw hz]
        exact Submodule.subset_span (by simp)
    · exact Submodule.span_le.mpr (by rintro w rfl; exact u.property)
  have hd := sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card (H := H)
  rw [he,finrank_span_singleton hun] at hd
  omega

/-- Every original quotient-point vector is fixed by its source Sylow subgroup. -/
theorem plane_vector_fixed
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (t : H) (ht : (t : G) ∈ (T : Subgroup G))
    (u : Additive (Section08.Source.Utilde H V₃ V₁))
    (hu : u ∈ sectionImage H V₃ V₁ V₂) (hu0 : u ≠ 0) :
    ρ (QuotientGroup.mk' (pCore 2 H) t) u = u := by
  have hs := sectionImage_invariant ρ hρ V₂ t (d.plane_stable ht) u hu
  have he : sectionImage H V₃ V₁ V₂ = Submodule.span (ZMod 2) {u} :=
    (eq_span_singleton_of_mem_of_finrank_eq_one (plane_section_finrank d) hu hu0)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (he ▸ hs)
  have hac : a = 0 ∨ a = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a
  rcases hac with rfl | rfl
  · have hz : ρ (QuotientGroup.mk' (pCore 2 H) t) u = 0 := by simpa using ha.symm
    exact (hu0 ((ρ.apply_bijective _).1 (hz.trans (map_zero _).symm))).elim
  · simpa using ha.symm

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
