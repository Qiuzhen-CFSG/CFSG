module

public import Theory.Representation.BinaryNaturalDual.FourActors.A2Module.CoreReduction.Geometry
public import Theory.Representation.RegularCyclicNormalClosure.Defs

/-!
# The common mixed sum is the actual displacement span

An outer involution has fixed space equal to its displacement image. Together
with one inner nontransvection this supplies both summands of the mixed space.
Conversely, the index-two coset decomposition confines every displacement to
that sum. Its intersection has dimension two, so the sum has dimension six.

Source: Aschbacher–Smith H.9.3(6), printed pp.391–392 (PDF pp.402–403).
All natural geometric premises remain explicit through Geometry.
-/

@[expose] public section
namespace BinaryNaturalDual.FourActors.A2Module.CoreReduction
open BinaryLinear BinaryLinear.OuterCyclic Subgroup
open Representation.RegularCyclicNormalClosure

/-- The mixed sum for a specified outer actor. -/
noncomputable def mixedSpace (d : CoordinateAction 4) (a : M) : Submodule (ZMod 2) V :=
  actorFixed d B2 ⊔ BinaryNaturalDual.fixedSpace (action d a)

theorem outer_not_inner {a : M} (ha : a ∈ A2) (haB : a ∉ B2) : a ∉ inner :=
  fun hi => haB ⟨ha, hi⟩

theorem outer_difference_mem {a c : M} (ha : a ∈ A2) (haB : a ∉ B2)
    (hc : c ∈ A2) (hcB : c ∉ B2) : c * a⁻¹ ∈ B2 := by
  refine ⟨A2.mul_mem hc (A2.inv_mem ha), ?_⟩
  apply (Subgroup.mul_mem_iff_of_index_two inner_index).mpr
  exact iff_of_false (outer_not_inner hc hcB)
    (by simpa only [Subgroup.inv_mem_iff] using outer_not_inner ha haB)

/-- Fixing B2 and one outer actor is exactly fixing A2. -/
theorem fixed_inter_eq (d : CoordinateAction 4) {a : M} (ha : a ∈ A2) (haB : a ∉ B2) :
    actorFixed d B2 ⊓ BinaryNaturalDual.fixedSpace (action d a) = actorFixed d A2 := by
  ext v
  simp only [Submodule.mem_inf, mem_actorFixed, mem_fixedSpace, action_apply]
  constructor
  · rintro ⟨hB, hA⟩ c hc
    by_cases hcB : c ∈ B2
    · exact hB c hcB
    · calc
        d.representation c v = d.representation (c * a⁻¹) (d.representation a v) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        _ = v := by rw [hA, hB _ (outer_difference_mem ha haB hc hcB)]
  · intro hv
    exact ⟨fun c hc => hv c hc.1, hv a ha⟩

variable [IsElementaryAbelian 2 A2]

namespace Geometry
variable {U : Submodule (ZMod 2) X} (h : Geometry U)
include h

theorem full_fixed_dimension (d : CoordinateAction 4) :
    Module.finrank (ZMod 2) (actorFixed d A2) = 2 := by
  rw [actorFixed_A2_finrank, h.naturalFixed_dimension]

/-- The mixed sum has the source's dimension six. -/
theorem mixed_dimension (d : CoordinateAction 4) {a : M} (ha : a ∈ A2) (haB : a ∉ B2) :
    Module.finrank (ZMod 2) (mixedSpace d a) = 6 := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (actorFixed d B2) (BinaryNaturalDual.fixedSpace (action d a))
  rw [fixed_inter_eq d ha haB, h.actorFixed_dimension d, h.full_fixed_dimension d,
    outer_fixedSpace_finrank d a (elemPow_eq_one_of_isElementaryAbelian a ha)
      (outer_not_inner ha haB)] at hd
  exact Nat.add_right_cancel hd

omit h [IsElementaryAbelian 2 A2] in
/-- Every actor displacement lies in the actual displacement span. -/
theorem range_le_displacement (d : CoordinateAction 4) {a : M} (ha : a ∈ A2) :
    LinearMap.range (d.representation a - LinearMap.id) ≤
      displacementSpan d.representation A2 ⊤ := by
  rintro v ⟨w, rfl⟩
  exact Submodule.subset_span ⟨a, ha, w, Submodule.mem_top, rfl⟩

/-- The common B2-fixed module and the outer fixed module are both displacements. -/
theorem mixed_le_displacement (d : CoordinateAction 4) {a : M}
    (ha : a ∈ A2) (haB : a ∉ B2) :
    mixedSpace d a ≤ displacementSpan d.representation A2 ⊤ := by
  apply sup_le
  · obtain ⟨g, hg, hg1, hgt⟩ := h.other_exists
    rw [← h.other_actor_range_eq d hg hg1 hgt]
    exact range_le_displacement d hg.1
  · rw [outer_fixedSpace_eq_displacement d a
      (elemPow_eq_one_of_isElementaryAbelian a ha) (outer_not_inner ha haB)]
    exact range_le_displacement d ha

/-- Decomposing an outer actor into the B2 coset bounds every displacement. -/
theorem displacement_le_mixed (d : CoordinateAction 4) {a : M}
    (ha : a ∈ A2) (haB : a ∉ B2) :
    displacementSpan d.representation A2 ⊤ ≤ mixedSpace d a := by
  apply Submodule.span_le.mpr
  rintro v ⟨c, hc, w, _, rfl⟩
  by_cases hcB : c ∈ B2
  · exact Submodule.mem_sup_left (h.inner_displacement_mem d hcB w)
  · have hb := outer_difference_mem ha haB hc hcB
    have he : d.representation c w - w =
        (d.representation (c * a⁻¹) (d.representation a w) - d.representation a w) +
          (d.representation a w - w) := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      abel
    rw [he]
    apply (mixedSpace d a).add_mem
    · exact Submodule.mem_sup_left (h.inner_displacement_mem d hb _)
    · apply Submodule.mem_sup_right
      rw [outer_fixedSpace_eq_displacement d a
        (elemPow_eq_one_of_isElementaryAbelian a ha) (outer_not_inner ha haB)]
      exact ⟨w, rfl⟩

/-- The mixed sum is the literal module commutator [V,A2]. -/
theorem mixed_eq_displacement (d : CoordinateAction 4) {a : M}
    (ha : a ∈ A2) (haB : a ∉ B2) :
    mixedSpace d a = displacementSpan d.representation A2 ⊤ :=
  le_antisymm (h.mixed_le_displacement d ha haB) (h.displacement_le_mixed d ha haB)

/-- Changing the outer actor does not change the mixed sum. -/
theorem mixed_independent (d : CoordinateAction 4) {a a' : M}
    (ha : a ∈ A2) (haB : a ∉ B2) (ha' : a' ∈ A2) (haB' : a' ∉ B2) :
    mixedSpace d a = mixedSpace d a' := by
  rw [h.mixed_eq_displacement d ha haB, h.mixed_eq_displacement d ha' haB']

end Geometry
end BinaryNaturalDual.FourActors.A2Module.CoreReduction
