module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Data
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates

/-!
# Conjugacy coverage in the actual binary local kernel

The certified parent tree covers all 2048 masks. Induction on its depth
composes actual local conjugations to reach mask 1 or 3, except at the
identity. The coordinate equivalence transfers this to every nonidentity
element of the normal closure. The two roots are the seed words whose
ambient fusion is checked in `Max1Fusion.Seeds`.

Source: ATLAS `J4G1-max1W1` and the concrete kernel conjugation tables
documented in `Cardinality.LocalOrder.KernelCount.Tables`.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
public section
namespace Janko4.Simplicity.Max1Fusion
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image KernelOrbits
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private theorem mask_orbits (m : Fin 2048) :
    (maskValue hA hB m.val : max1Subgroup hA hB) = 1 ∨
    IsConj (maskValue hA hB m.val : max1Subgroup hA hB) (localKernelSeed hA hB) ∨
    IsConj (maskValue hA hB m.val : max1Subgroup hA hB) (kernelPair hA hB) := by
  suffices ∀ d (m : Fin 2048), depth m = d →
      (maskValue hA hB m.val : max1Subgroup hA hB) = 1 ∨
      IsConj (maskValue hA hB m.val : max1Subgroup hA hB) (localKernelSeed hA hB) ∨
      IsConj (maskValue hA hB m.val : max1Subgroup hA hB) (kernelPair hA hB) from
    this (depth m) m rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m hm
    rcases tree_certificate m with h0 | h1 | h3 | ⟨hd, he⟩
    · subst m
      exact Or.inl (congrArg (fun z : localKernel hA hB => (z : max1Subgroup hA hB))
        (maskValue_zero hA hB))
    · subst m
      exact Or.inr (Or.inl ((maskValue_one hA hB) ▸ IsConj.refl _))
    · subst m
      exact Or.inr (Or.inr ((maskValue_three hA hB) ▸ IsConj.refl _))
    · have hc : IsConj (maskValue hA hB (parent m).val : max1Subgroup hA hB)
          (maskValue hA hB m.val : max1Subgroup hA hB) := by
        rcases he with hx | hy
        · exact isConj_iff.mpr ⟨(localX hA hB)⁻¹, by
            simpa only [inv_inv, hx] using right_conj_mask_x hA hB (parent m).val⟩
        · exact isConj_iff.mpr ⟨(localY hA hB)⁻¹, by
            simpa only [inv_inv, hy] using right_conj_mask_y hA hB (parent m).val⟩
      rcases ih (depth (parent m)) (hd.trans_eq hm) (parent m) rfl with h0 | h1 | h3
      · obtain ⟨g, hg⟩ := isConj_iff.mp hc
        rw [h0, mul_one, mul_inv_cancel] at hg
        exact Or.inl hg.symm
      · exact Or.inr (Or.inl (hc.symm.trans h1))
      · exact Or.inr (Or.inr (hc.symm.trans h3))

/-- Every nonidentity element of the actual local kernel is locally conjugate
 to one of the two explicit seed words. -/
theorem kernel_nonidentity_orbits (z : max1Subgroup hA hB)
    (hz : z ∈ localKernel hA hB) (hne : z ≠ 1) :
    ∃ g : max1Subgroup hA hB,
      localKernelSeed hA hB = g * z * g⁻¹ ∨ kernelPair hA hB = g * z * g⁻¹ := by
  obtain ⟨m, hm⟩ := maskValue_surjective hA hB ⟨z, hz⟩
  have he : (maskValue hA hB m.val : max1Subgroup hA hB) = z :=
    congrArg (fun n : localKernel hA hB => (n : max1Subgroup hA hB)) hm
  rcases mask_orbits hA hB m with h0 | h1 | h3
  · exact (hne (he.symm.trans h0)).elim
  · rw [he] at h1
    obtain ⟨g, hg⟩ := isConj_iff.mp h1
    exact ⟨g, Or.inl hg.symm⟩
  · rw [he] at h3
    obtain ⟨g, hg⟩ := isConj_iff.mp h3
    exact ⟨g, Or.inr hg.symm⟩

/-- The kernel branch of the local involution fusion problem. -/
theorem kernel_involution_orbits (z : max1Subgroup hA hB)
    (hz : z ∈ localKernel hA hB) (ho : orderOf z = 2) :
    ∃ g : max1Subgroup hA hB,
      localKernelSeed hA hB = g * z * g⁻¹ ∨ kernelPair hA hB = g * z * g⁻¹ := by
  apply kernel_nonidentity_orbits hA hB z hz
  intro he
  rw [he, orderOf_one] at ho
  omega

end Janko4.Simplicity.Max1Fusion
