module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Data
/-! The two Frobenius functionals and their bilinear expansion.
Source and witness conventions: Reconstruction/source/README.md. -/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

def lj := functional (decode functionalJBits : RestrictionMatrix)
def le := functional (decode functionalEBits : RestrictionMatrix)

def bilinear (X Y : RestrictionMatrix) : ZMod 2 :=
  lj (Xᵀ * restrictionPairing * Y) + le (Xᵀ * restrictionTestForm 0 * Y)

theorem bilinear_add_left (X Y Z : RestrictionMatrix) :
    bilinear (X + Y) Z = bilinear X Z + bilinear Y Z := by
  simp only [bilinear, Matrix.transpose_add, Matrix.add_mul, map_add]
  ring

theorem bilinear_add_right (X Y Z : RestrictionMatrix) :
    bilinear X (Y + Z) = bilinear X Y + bilinear X Z := by
  simp only [bilinear, Matrix.mul_add, map_add]
  ring

theorem bilinear_zero_left (X : RestrictionMatrix) : bilinear 0 X = 0 := by
  simp [bilinear]
theorem bilinear_zero_right (X : RestrictionMatrix) : bilinear X 0 = 0 := by
  simp [bilinear]

theorem bilinear_smul_left (c : ZMod 2) (X Y : RestrictionMatrix) :
    bilinear (c • X) Y = c * bilinear X Y := by
  simp [bilinear, Matrix.transpose_smul, smul_eq_mul, mul_add]

theorem bilinear_smul_right (c : ZMod 2) (X Y : RestrictionMatrix) :
    bilinear X (c • Y) = c * bilinear X Y := by
  simp [bilinear, smul_eq_mul, mul_add]

theorem bilinear_weight (X Y : RestrictionMatrix) :
    bilinear X Y = pairing
      (restrictionPairingᵀ * X * decode functionalJBits +
       (restrictionTestForm 0)ᵀ * X * decode functionalEBits) Y := by
  change pairing (decode functionalJBits) (Xᵀ * restrictionPairing * Y) +
    pairing (decode functionalEBits) (Xᵀ * restrictionTestForm 0 * Y) = _
  rw [pairing_mul_right, pairing_mul_right, ← pairing_add_left]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem decode_xor {m n : ℕ} (x y : ℕ) :
    (decode (x ^^^ y) : Matrix (Fin m) (Fin n) (ZMod 2)) = decode x + decode y := by
  ext i j
  exact bit_xor _ _ _

theorem pairing_restriction (F : RestrictionMatrix) (A : BinaryMatrix) :
    pairing F (restrictionForm A) =
      pairing (restrictionEmbedding * F * restrictionEmbeddingᵀ) A := by
  unfold restrictionForm
  rw [pairing_mul_left, pairing_mul_right]
  simp only [Matrix.transpose_transpose, Matrix.mul_assoc]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
