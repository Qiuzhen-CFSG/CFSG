module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.GeneratorRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Canonical

/-!
# Matrices of the actual eight native generators

Kernel-checked products evaluate the two nonsingleton kernel masks. Together
with the existing corrected-lift evaluations, these identify all eight source
generators in the original 112-dimensional representation. The six products
were measured as a bounded batch before the layer calculations.
Source: Kleidman--Wilson (1988), Figures 1/2 and Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open Cardinality KernelCount GeneratorCertificates
open KernelCount.Relations (eval_mul decoded_product)
open Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "ρ" => representation matrixA_mul_self matrixB_pow_four

private theorem eval_basis (i : Fin 11) :
    ρ (nativeMask (2^i.val)) = decodeRows (basisRows i) := by
  rw [show nativeMask (2^i.val) = basis matrixA_mul_self matrixB_pow_four i from
    maskValue_basis matrixA_mul_self matrixB_pow_four i]
  exact representation_basis _ _ i

private theorem product48 : packedMul (basisRows 4) (basisRows 5) = kernel48Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
private theorem product304 : packedMul kernel48Rows (basisRows 8) = kernel304Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
private theorem product816 : packedMul kernel304Rows (basisRows 9) = kernel816Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
private theorem product40 : packedMul (basisRows 3) (basisRows 5) = kernel40Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
private theorem product104 : packedMul kernel40Rows (basisRows 6) = kernel104Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
private theorem product1128 : packedMul kernel104Rows (basisRows 10) = kernel1128Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

private theorem eval48 : ρ (nativeMask 48) = decodeRows kernel48Rows := by
  rw [show nativeMask 48 = nativeMask 16 * nativeMask 32 from nativeMask_xor 16 32]
  exact eval_mul ρ (eval_basis 4) (eval_basis 5) (decoded_product product48)
private theorem eval304 : ρ (nativeMask 304) = decodeRows kernel304Rows := by
  rw [show nativeMask 304 = nativeMask 48 * nativeMask 256 from nativeMask_xor 48 256]
  exact eval_mul ρ eval48 (eval_basis 8) (decoded_product product304)
private theorem eval816 : ρ (nativeMask 816) = decodeRows kernel816Rows := by
  rw [show nativeMask 816 = nativeMask 304 * nativeMask 512 from nativeMask_xor 304 512]
  exact eval_mul ρ eval304 (eval_basis 9) (decoded_product product816)
private theorem eval40 : ρ (nativeMask 40) = decodeRows kernel40Rows := by
  rw [show nativeMask 40 = nativeMask 8 * nativeMask 32 from nativeMask_xor 8 32]
  exact eval_mul ρ (eval_basis 3) (eval_basis 5) (decoded_product product40)
private theorem eval104 : ρ (nativeMask 104) = decodeRows kernel104Rows := by
  rw [show nativeMask 104 = nativeMask 40 * nativeMask 64 from nativeMask_xor 40 64]
  exact eval_mul ρ eval40 (eval_basis 6) (decoded_product product104)
private theorem eval1128 : ρ (nativeMask 1128) = decodeRows kernel1128Rows := by
  rw [show nativeMask 1128 = nativeMask 104 * nativeMask 1024 from nativeMask_xor 104 1024]
  exact eval_mul ρ eval104 (eval_basis 10) (decoded_product product1128)

/-- These are exactly the original matrices of the eight actual native generators. -/
theorem toMatrix_nativeGenerator (i : Fin 8) : toMatrix (nativeGenerator i) = decodeRows (generatorRows i) := by
  fin_cases i
  · exact eval_basis 0
  · exact eval_basis 1
  · exact eval816
  · exact eval1128
  · exact representation_correctedLift 0
  · exact representation_correctedLift 1
  · exact representation_correctedLift 2
  · exact representation_correctedLift 5

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
