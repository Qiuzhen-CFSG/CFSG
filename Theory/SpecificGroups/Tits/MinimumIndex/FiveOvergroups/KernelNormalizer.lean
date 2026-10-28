module
public import Theory.SpecificGroups.Tits.MinimumIndex.Candidates
public import Theory.SpecificGroups.Tits.FiveFrobenius.Subgroups
import all Theory.SpecificGroups.Tits.FiveFrobenius.Subgroups

/-!
# The marked five-kernel inside the literal max8 candidate

The kernel generators are ATLAS max8 words. Four kernel-checked permutation
identities show that each max8 generator conjugates them back into the kernel.
Finite-order conjugation then gives normalization of the whole kernel.

The private import deliberately accesses the defining closure of the kernel
for this internal Tits proof extension. The closure equation, containment and normalization
theorems are exported; the existing FiveFrobenius public boundary is unchanged.
Source: primary ATLAS `TF42G1-max8W1`, preserved in `MinimumIndex/source/`,
and the existing checked word tables in `FiveFrobenius.WordCertificate`.
-/

namespace Tits.MinimumIndexFiveOvergroups
open Subgroup MinimumIndexCandidates FiveFrobenius Atlas1600ParrottData
set_option maxRecDepth 20000

/-- The precise generating set of the marked kernel, for word-certificate
consumers which should not need access to its private implementation. -/
public theorem kernel_eq_closure : kernel = closure ({v, u} : Set Atlas1600Group) := by
  rfl

private theorem max8_second_val : max8Generators.2.val = x2p := by
  let q : Equiv.Perm (Fin 1600) := (atlas1600A * atlas1600B) *
    ((atlas1600A * atlas1600B) * atlas1600B)
  rw [x2p_word]
  change (q * (q * q))⁻¹ * atlas1600B * (q * (q * q)) = _
  simp [q, pow_succ, mul_assoc]

private theorem a_conj_u : max8Generators.1 * u * max8Generators.1⁻¹ = u ^ 3 * v := by
  apply Subtype.ext
  change atlas1600A * u.val * atlas1600A⁻¹ = u.val ^ 3 * v.val
  rw [u_val, v_val, atlasA_word]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem a_conj_v : max8Generators.1 * v * max8Generators.1⁻¹ = u ^ 2 * v ^ 2 := by
  apply Subtype.ext
  change atlas1600A * v.val * atlas1600A⁻¹ = u.val ^ 2 * v.val ^ 2
  rw [u_val, v_val, atlasA_word]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem x2_conj_u : max8Generators.2 * u * max8Generators.2⁻¹ = u * v := by
  apply Subtype.ext
  change max8Generators.2.val * u.val * max8Generators.2.val⁻¹ = u.val * v.val
  rw [max8_second_val, u_val, v_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem x2_conj_v : max8Generators.2 * v * max8Generators.2⁻¹ = u ^ 2 * v ^ 3 := by
  apply Subtype.ext
  change max8Generators.2.val * v.val * max8Generators.2.val⁻¹ = u.val ^ 2 * v.val ^ 3
  rw [max8_second_val, u_val, v_val]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- The literal max8 candidate normalizes the marked five-kernel. -/
public theorem max8_normalizes_kernel : max8 ≤ normalizer (kernel : Set Atlas1600Group) := by
  rw [kernel_eq_closure]
  have hu : u ∈ closure ({v, u} : Set Atlas1600Group) := subset_closure (by simp)
  have hv : v ∈ closure ({v, u} : Set Atlas1600Group) := subset_closure (by simp)
  apply (closure_le _).mpr
  rintro a (rfl | rfl)
  · apply normalizes_closure
    rintro z (rfl | rfl)
    · rw [a_conj_v]
      exact mul_mem (pow_mem hu _) (pow_mem hv _)
    · rw [a_conj_u]
      exact mul_mem (pow_mem hu _) hv
  · apply normalizes_closure
    rintro z (rfl | rfl)
    · rw [x2_conj_v]
      exact mul_mem (pow_mem hu _) (pow_mem hv _)
    · rw [x2_conj_u]
      exact mul_mem hu hv

/-- The kernel's defining words are words in the literal max8 generators. -/
public theorem kernel_le_max8 : kernel ≤ max8 := by
  rw [kernel_eq_closure]
  have ha : max8Generators.1 ∈ max8 := subset_closure (by simp)
  have hb : max8Generators.2 ∈ max8 := subset_closure (by simp)
  apply (closure_le _).mpr
  rintro z (rfl | rfl)
  · have hv : v = max8Generators.2 * max8Generators.1⁻¹ * max8Generators.2⁻¹ *
        (max8Generators.1⁻¹ * max8Generators.2) ^ 2 *
        (max8Generators.1⁻¹ * max8Generators.2⁻¹) ^ 5 := by
      apply Subtype.ext
      change v.val = max8Generators.2.val * atlas1600A⁻¹ * max8Generators.2.val⁻¹ *
        (atlas1600A⁻¹ * max8Generators.2.val) ^ 2 *
        (atlas1600A⁻¹ * max8Generators.2.val⁻¹) ^ 5
      rw [v_val, max8_second_val, vp_word]
    rw [hv]
    exact mul_mem (mul_mem (mul_mem (mul_mem hb (inv_mem ha)) (inv_mem hb))
      (pow_mem (mul_mem (inv_mem ha) hb) _))
      (pow_mem (mul_mem (inv_mem ha) (inv_mem hb)) _)
  · have hu : u = max8Generators.2⁻¹ * max8Generators.1⁻¹ * max8Generators.2 *
        max8Generators.1⁻¹ * max8Generators.2 *
        (max8Generators.1⁻¹ * max8Generators.2⁻¹) ^ 4 := by
      apply Subtype.ext
      change u.val = max8Generators.2.val⁻¹ * atlas1600A⁻¹ * max8Generators.2.val *
        atlas1600A⁻¹ * max8Generators.2.val *
        (atlas1600A⁻¹ * max8Generators.2.val⁻¹) ^ 4
      rw [u_val, max8_second_val, up_word]
    rw [hu]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hb) (inv_mem ha)) hb)
      (inv_mem ha)) hb) (pow_mem (mul_mem (inv_mem ha) (inv_mem hb)) _)

end Tits.MinimumIndexFiveOvergroups
