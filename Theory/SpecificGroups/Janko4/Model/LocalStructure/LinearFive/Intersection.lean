module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Elementary

/-!
# The exact intersection with the native Mathieu kernel

Restrict the genuine max1 quotient to the constructed F. Its image has order
16, while F has order 1024, so its kernel has order 64. The final map theorem
identifies that kernel with the literal ambient intersection F ∩ E.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality Subgroup
open Sporadic.Mathieu
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

def localFProjection : localF →* M24 := projection.comp localF.subtype

theorem localFProjection_range : localFProjection.range = A := by
  rw [localFProjection, MonoidHom.range_comp, Subgroup.range_subtype, localF_image]

theorem localFProjection_ker_card : Nat.card localFProjection.ker = 64 := by
  have h := localFProjection.ker.card_mul_index
  rw [Subgroup.index_ker, localFProjection_range, A_card, localF_card] at h
  omega

/-- The restricted quotient kernel maps to the actual intersection in J4. -/
theorem localFProjection_ker_map :
    localFProjection.ker.map (M.subtype.comp localF.subtype) = F ⊓ E := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    constructor
    · exact Subgroup.mem_map.mpr ⟨(a : M), a.property, rfl⟩
    · apply Subgroup.mem_map.mpr
      refine ⟨(a : M), ?_, rfl⟩
      rw [← MathieuHallActors.projection_ker, MonoidHom.mem_ker]
      exact ha
  · rintro ⟨hf, he⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hf
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp he
    have hba' : b = a := M.subtype_injective hba
    subst b
    refine Subgroup.mem_map.mpr ⟨⟨a, ha⟩, ?_, rfl⟩
    change projection a = 1
    apply MonoidHom.mem_ker.mp
    rw [MathieuHallActors.projection_ker]
    exact hb

theorem F_inf_E_card : Nat.card (F ⊓ E : Subgroup Model) = 64 := by
  have hi : Function.Injective (M.subtype.comp localF.subtype) := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  rw [← localFProjection_ker_map,
    Subgroup.card_map_of_injective hi, localFProjection_ker_card]

end Janko4.LocalStructure.LinearFive
