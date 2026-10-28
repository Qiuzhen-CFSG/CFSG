module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Coordinates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowData

/-!
# The image of the native generators in the marked Mathieu quotient

The literal ATLAS local generators map to the certified star generators. This
identifies the four chosen native words with four permutations fixing the
standard octad pointwise; the kernel corrections do not change those images.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount QuotientCount QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits Simplicity.Max1Fusion.QuotientInvolutions
open Sporadic.Mathieu MathieuCode
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis

private theorem projection_x :
    projection (localX matrixA_mul_self matrixB_pow_four) = starGroupEquivM24 starFirst := by
  change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
    (QuotientGroup.mk' _ (localX matrixA_mul_self matrixB_pow_four)) = _
  rw [localQuotientEquivM24_apply]
  congr 1
  apply Subtype.ext
  exact actionImageEquivStarGroup_x matrixA_mul_self matrixB_pow_four

private theorem projection_y :
    projection (localY matrixA_mul_self matrixB_pow_four) = starGroupEquivM24 starSecond := by
  change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
    (QuotientGroup.mk' _ (localY matrixA_mul_self matrixB_pow_four)) = _
  rw [localQuotientEquivM24_apply]
  congr 1
  apply Subtype.ext
  exact actionImageEquivStarGroup_y matrixA_mul_self matrixB_pow_four

def quotientLift (i : Fin 4) : M24 :=
  starGroupEquivM24 (NativeWords.lifts starFirst starSecond i)

theorem projection_lift (i : Fin 4) : projection (lift i) = quotientLift i := by
  rw [lift, map_mul, projection_kernelValue, mul_one, NativeWords.map_lifts,
    projection_x, projection_y]
  exact (NativeWords.map_lifts starFirst starSecond starGroupEquivM24.toMonoidHom i).symm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem quotientLift_fixes :
    ∀ (j : Fin 4) (i : Fin 24), i ∈ (O : Set (Fin 24)) → (quotientLift j : Equiv.Perm (Fin 24)) i = i := by
  simp only [quotientLift, starGroupEquivM24_apply]
  decide +kernel

theorem lift_projection_mem_A (i : Fin 4) : projection (lift i) ∈ A := by
  rw [projection_lift]
  exact (mem_octadPointwiseKernel O _).mpr (quotientLift_fixes i)

theorem F_le_Q : F ≤ Q := by
  apply Subgroup.map_mono
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_ i
  · intro j
    simp only [generators, Fin.append_left]
    change projection (kernelValue (kernelMasks j)) ∈ A
    rw [projection_kernelValue]
    exact A.one_mem
  · intro j
    simp only [generators, Fin.append_right]
    exact lift_projection_mem_A j


private def quotientPermutationFunction : Fin 4 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 6, 9, 4, 21, 15, 5, 10, 19, 18, 20, 17, 8, 16, 14, 12, 11, 13, 7, 22, 23],
    ![0, 1, 2, 3, 5, 4, 9, 15, 21, 6, 10, 17, 20, 18, 19, 7, 16, 11, 13, 14, 12, 8, 22, 23],
    ![0, 1, 2, 3, 19, 14, 11, 13, 12, 17, 10, 6, 8, 7, 5, 18, 16, 9, 15, 4, 21, 20, 22, 23],
    ![0, 1, 2, 3, 21, 8, 7, 6, 5, 15, 10, 13, 14, 11, 12, 9, 16, 18, 17, 20, 19, 4, 22, 23]]
private def quotientPermutation (i : Fin 4) : Equiv.Perm (Fin 24) where
  toFun := quotientPermutationFunction i
  invFun := quotientPermutationFunction i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem quotientLift_perm (i : Fin 4) :
    (quotientLift i : Equiv.Perm (Fin 24)) = quotientPermutation i := by
  simp only [quotientLift, starGroupEquivM24_apply]
  fin_cases i <;> decide +kernel

/-- Each of the four actual lifts has nonidentity image in the genuine quotient. -/
theorem projection_lift_ne_one (i : Fin 4) : projection (lift i) ≠ 1 := by
  intro h
  have hp : (quotientLift i : Equiv.Perm (Fin 24)) = 1 :=
    congrArg (fun a : M24 => (a : Equiv.Perm (Fin 24))) ((projection_lift i).symm.trans h)
  rw [quotientLift_perm] at hp
  have hh : ∀ j : Fin 4, quotientPermutation j 4 ≠ 4 := by decide +kernel
  exact hh i (congrArg (fun a : Equiv.Perm (Fin 24) => a 4) hp)

private theorem quotient_binaryProduct_injective :
    Function.Injective (binaryProduct quotientLift) := by
  have hi : Function.Injective (fun v : Fin 4 → Bool =>
      binaryProduct quotientPermutation v 4) := by decide +kernel
  intro v w h
  apply hi
  have h' := congrArg (fun a : M24 => (a : Equiv.Perm (Fin 24))) h
  have hm (u : Fin 4 → Bool) :
      ((binaryProduct quotientLift u : M24) : Equiv.Perm (Fin 24)) =
        binaryProduct quotientPermutation u := by
    have hh := map_binaryProduct M24.subtype quotientLift u
    change ((binaryProduct quotientLift u : M24) : Equiv.Perm (Fin 24)) =
      binaryProduct (fun i => (quotientLift i : Equiv.Perm (Fin 24))) u at hh
    simpa only [quotientLift_perm] using hh
  rw [hm, hm] at h'
  exact congrArg (fun a : Equiv.Perm (Fin 24) => a 4) h'

private theorem quotientLift_square (i : Fin 4) : quotientLift i * quotientLift i = 1 := by
  apply Subtype.ext
  change (quotientLift i : Equiv.Perm (Fin 24)) * (quotientLift i : Equiv.Perm (Fin 24)) = 1
  rw [quotientLift_perm]
  fin_cases i <;> decide +kernel

private theorem quotientLift_commute (i j : Fin 4) : Commute (quotientLift i) (quotientLift j) := by
  apply Subtype.ext
  change (quotientLift i : Equiv.Perm (Fin 24)) * (quotientLift j : Equiv.Perm (Fin 24)) =
    (quotientLift j : Equiv.Perm (Fin 24)) * (quotientLift i : Equiv.Perm (Fin 24))
  simp only [quotientLift_perm]
  have h : ∀ i j : Fin 4, quotientPermutation i * quotientPermutation j =
      quotientPermutation j * quotientPermutation i := by decide +kernel
  exact h i j

/-- The four literal quotient words generate the entire octad pointwise kernel. -/
theorem quotientLift_generate : Subgroup.closure (Set.range quotientLift) = A := by
  have hle : Subgroup.closure (Set.range quotientLift) ≤ A := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    rw [← projection_lift]
    exact lift_projection_mem_A i
  have hc : Nat.card (Subgroup.closure (Set.range quotientLift)) = 16 :=
    card_closure_binaryProduct quotientLift quotientLift_square quotientLift_commute
      quotient_binaryProduct_injective
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, A_card])

/-- The constructed native subgroup has precisely the required quotient image. -/
theorem localF_image : localF.map projection = A := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases (m := 6) (n := 4) ?_ ?_ i
    · intro j
      simp only [generators, Fin.append_left]
      change projection (kernelValue (kernelMasks j)) ∈ A
      rw [projection_kernelValue]
      exact A.one_mem
    · intro j
      simp only [generators, Fin.append_right]
      exact lift_projection_mem_A j
  · rw [← quotientLift_generate]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    refine Subgroup.mem_map.mpr ⟨lift i, ?_, projection_lift i⟩
    have h := generator_mem_localF (Fin.natAdd 6 i)
    simpa only [generators, Fin.append_right] using h
end Janko4.LocalStructure.LinearFive
