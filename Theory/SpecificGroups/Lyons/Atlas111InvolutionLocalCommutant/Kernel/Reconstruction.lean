module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Inverse
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Columns

/-!
# Reconstruction from the annihilator equations

The inverse of the augmented matrix reconstructs a kernel vector from its
coordinates 0 and 2. Its last two columns give the coefficients in the span
of the seed and the involution's seed column.
Source and candidate generation: `Kernel/source/GenerateKernel.py`.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Kernel
open Atlas111WordCertificate Matrix

private theorem n_row (i : Fin 111) : nMatrix i =
    if i.val < 109 then rMatrix i else
      if i = 109 then (1 : AtlasMatrix) 0 else (1 : AtlasMatrix) 2 := by
  funext j
  unfold nMatrix decode nRows
  split_ifs
  · rfl
  · exact congrFun (congrFun oneMatrix_eq 0) j
  · exact congrFun (congrFun oneMatrix_eq 2) j

private theorem augmented_action (x : Fin 111 → ZMod 5) (hx : rMatrix *ᵥ x = 0) :
    nMatrix *ᵥ x = Pi.single 109 (x 0) + Pi.single 110 (x 2) := by
  funext i
  by_cases hi : i.val < 109
  · have hi109 : i ≠ 109 := by intro h; subst i; simp at hi
    have hi110 : i ≠ 110 := by intro h; subst i; simp at hi
    have heq : (nMatrix *ᵥ x) i = (rMatrix *ᵥ x) i := by
      simp only [mulVec, n_row, hi, ↓reduceIte]
    rw [heq, hx]
    simp [hi109, hi110]
  · have hcases : i = 109 ∨ i = 110 := by
      have hib := i.isLt
      apply or_iff_not_imp_left.mpr
      intro h
      apply Fin.ext
      have hn : i.val ≠ 109 := by intro he; apply h; exact Fin.ext he
      omega
    rcases hcases with rfl | rfl <;>
      simp [mulVec, n_row, dotProduct, Matrix.one_apply]

/-- A vector killed by the candidate annihilator is determined by coordinates 0 and 2. -/
public theorem reconstruct (x : Fin 111 → ZMod 5) (hx : rMatrix *ᵥ x = 0) :
    x = (x 0 + 3 * x 2) • (localSeed (n := 111) (K := ZMod 5)) +
      (4 * x 2) • (ab7Matrix *ᵥ (localSeed (n := 111) (K := ZMod 5))) := by
  have hrecon : x = dMatrix *ᵥ (nMatrix *ᵥ x) := by
    rw [mulVec_mulVec, inverse_mul, one_mulVec]
  rw [augmented_action x hx, mulVec_add] at hrecon
  have hsingle (j : Fin 111) (a : ZMod 5) :
      dMatrix *ᵥ Pi.single j a = a • (fun i => dMatrix i j) := by
    ext i
    simp [mulVec_single, col_apply, mul_comm]
  rw [hsingle, hsingle, inverse_seed_column, inverse_t_column] at hrecon
  conv_lhs => rw [hrecon]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The only remaining numerical premise is the identification of the word polynomial. -/
public theorem certificate_of_polynomial
    (hpoly : localAnnihilator abMatrix Words.localBMatrix coefficients = rMatrix) :
    InvolutionLocalKernelCertificate := by
  unfold InvolutionLocalKernelCertificate
  rw [Words.image_localA, Words.image_localB, Words.image_t]
  refine ⟨coefficients, ?_, ?_⟩
  · rw [hpoly]
    exact annihilates_seed
  · intro x hx
    rw [hpoly] at hx
    exact ⟨x 0 + 3 * x 2, 4 * x 2, reconstruct x hx⟩

end Lyons.SimplicityCertificate.LocalCommutant.Kernel
