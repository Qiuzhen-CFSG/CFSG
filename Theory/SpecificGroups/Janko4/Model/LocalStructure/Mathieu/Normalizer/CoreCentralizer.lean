module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder

/-!
# The ambient centralizer of the literal max1 kernel

Let M be the literal ATLAS max1 subgroup and E the ambient image of its
order-2048 local kernel. The seed `(xy)^14` belongs to E, so every element
centralizing E centralizes the seed. The proved full seed-centralizer order
bound places that element in M. The intrinsic identity C_M(E) = E then gives
the ambient identity C_Model(E) = E.

This supplies the centralizer part of the max1 normalizer calculation in
GLS3, Table 5.3i, printed p.270. The literal matrix-word provenance is recorded
in `Cardinality.Subgroup`; all seed-centralizer premises are discharged by
`MathieuSeedCentralizer.AmbientOrder`.
-/

public section

open Subgroup
namespace Janko4.LocalStructure
open Cardinality MathieuSeedCentralizer

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localKernelSeed

/-- Centralizing the embedded kernel forces membership in the literal max1 subgroup. -/
theorem centralizer_embedded_localKernel_le_max1 :
    centralizer ((localKernel matrixA_mul_self matrixB_pow_four).map
      (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype : Set Model) ≤
        max1Subgroup matrixA_mul_self matrixB_pow_four := by
  intro g hg
  apply ambientSeedCentralizer_le_max1_of_card_le matrixA_mul_self matrixB_pow_four
    ambientSeedCentralizer_card_le
  intro t ht
  obtain rfl := Set.mem_singleton_iff.mp ht
  exact hg _ ⟨_, localKernelSeed_mem _ _, rfl⟩

/-- The actual order-2048 kernel is self-centralizing in the full matrix model. -/
theorem centralizer_embedded_localKernel :
    centralizer ((localKernel matrixA_mul_self matrixB_pow_four).map
      (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype : Set Model) =
        (localKernel matrixA_mul_self matrixB_pow_four).map
          (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype := by
  apply le_antisymm
  · intro g hg
    let gM : max1Subgroup matrixA_mul_self matrixB_pow_four :=
      ⟨g, centralizer_embedded_localKernel_le_max1 hg⟩
    have hlocal : gM ∈ centralizer (localKernel matrixA_mul_self matrixB_pow_four :
        Set (max1Subgroup matrixA_mul_self matrixB_pow_four)) := by
      intro x hx
      apply Subtype.ext
      exact hg _ ⟨x, hx, rfl⟩
    rw [centralizer_localKernel] at hlocal
    exact ⟨gM, hlocal, rfl⟩
  · rintro g ⟨g, hg, rfl⟩ x ⟨x, hx, rfl⟩
    have hc : g ∈ centralizer (localKernel matrixA_mul_self matrixB_pow_four :
        Set (max1Subgroup matrixA_mul_self matrixB_pow_four)) := by
      rwa [centralizer_localKernel]
    exact congrArg (fun z : max1Subgroup matrixA_mul_self matrixB_pow_four => (z : Model))
      (hc x hx)

end Janko4.LocalStructure
