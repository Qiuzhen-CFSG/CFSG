module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorSpace

/-!
# Linear constraints on pointwise-fixed shears

Transport the independently defined exterior-form space through the certified
basis. A shear preserving this whole space has `R H` in the mixed-block image
of the forms with zero upper-left block, for every restriction `R`. Subtracting
a form from its pullback proves this necessary condition without any quadratic
classification. Preservation of the actual invariant pairing also makes `J H`
symmetric.

Source: the block pullback identity and the ATLAS form certificates imported
by `Coordinates.Calibration`. The finite two-test completeness calculation is
a separate obligation; this module proves the linear tests for all forms.
-/

@[expose] public section

open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates
open Matrix
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

def formCoordinates (F : BinaryMatrix) : BlockMatrix :=
  blockReindex (adaptedBasisᵀ * F * adaptedBasis)

theorem blockReindex_transpose (F : BinaryMatrix) : blockReindex Fᵀ = (blockReindex F)ᵀ := rfl

theorem basis_mul_conjugate (g : BinaryMatrix) :
    adaptedBasis * conjugateMatrix g = g * adaptedBasis := by
  dsimp [conjugateMatrix]
  rw [← mul_assoc, ← mul_assoc, show adaptedBasis * adaptedBasisInverse = 1 from adapted_mul_inverse,
    one_mul]

theorem formCoordinates_pullback (g F : BinaryMatrix) :
    formCoordinates (gᵀ * F * g) =
      (blockCoordinates g)ᵀ * formCoordinates F * blockCoordinates g := by
  have h : (conjugateMatrix g)ᵀ * (adaptedBasisᵀ * F * adaptedBasis) * conjugateMatrix g =
      adaptedBasisᵀ * (gᵀ * F * g) * adaptedBasis := by
    calc
      _ = (adaptedBasis * conjugateMatrix g)ᵀ * F *
          (adaptedBasis * conjugateMatrix g) := by simp only [transpose_mul, mul_assoc]
      _ = (g * adaptedBasis)ᵀ * F * (g * adaptedBasis) := by rw [basis_mul_conjugate]
      _ = _ := by simp only [transpose_mul, mul_assoc]
  simpa only [formCoordinates, blockCoordinates, map_mul, blockReindex_transpose] using
    congrArg blockReindex h.symm

theorem blockReindex_smul (r : ZMod 2) (F : BinaryMatrix) :
    blockReindex (r • F) = r • blockReindex F := rfl

def formCoordinatesLinear : BinaryMatrix →ₗ[ZMod 2] BlockMatrix where
  toFun := formCoordinates
  map_add' F R := by simp only [formCoordinates, mul_add, add_mul, map_add]
  map_smul' r F := by
    change blockReindex (adaptedBasisᵀ * (r • F) * adaptedBasis) =
      r • blockReindex (adaptedBasisᵀ * F * adaptedBasis)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact blockReindex_smul r _

def adaptedExteriorSpace : Submodule (ZMod 2) BlockMatrix :=
  exteriorFormSpace.map formCoordinatesLinear

def upperBlockLinear : BlockMatrix →ₗ[ZMod 2] HalfMatrix where
  toFun := Matrix.toBlocks₁₁
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mixedBlockLinear : BlockMatrix →ₗ[ZMod 2] HalfMatrix where
  toFun := Matrix.toBlocks₁₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mixedKernelSpace : Submodule (ZMod 2) HalfMatrix :=
  (adaptedExteriorSpace ⊓ LinearMap.ker upperBlockLinear).map mixedBlockLinear

def shearMatrix (H : HalfMatrix) : BlockMatrix := Matrix.fromBlocks 1 H 0 1

theorem shear_pullback (R S U T H : HalfMatrix) :
    (shearMatrix H)ᵀ * Matrix.fromBlocks R S U T * shearMatrix H =
      Matrix.fromBlocks R (R * H + S) (Hᵀ * R + U)
        ((Hᵀ * R + U) * H + (Hᵀ * S + T)) := by
  simp only [shearMatrix, Matrix.fromBlocks_transpose, transpose_one, transpose_zero,
    Matrix.fromBlocks_multiply, one_mul, zero_mul, mul_one, mul_zero, add_zero]

theorem shear_mixed_constraint (H : HalfMatrix)
    (hH : ∀ F ∈ adaptedExteriorSpace, (shearMatrix H)ᵀ * F * shearMatrix H ∈ adaptedExteriorSpace)
    (F : BlockMatrix) (hF : F ∈ adaptedExteriorSpace) :
    F.toBlocks₁₁ * H ∈ mixedKernelSpace := by
  have hupper : upperBlockLinear ((shearMatrix H)ᵀ * F * shearMatrix H) = upperBlockLinear F := by
    rw [← Matrix.fromBlocks_toBlocks F, shear_pullback]
    rfl
  have hmixed : mixedBlockLinear ((shearMatrix H)ᵀ * F * shearMatrix H) =
      F.toBlocks₁₁ * H + mixedBlockLinear F := by
    rw [← Matrix.fromBlocks_toBlocks F, shear_pullback]
    rfl
  refine ⟨(shearMatrix H)ᵀ * F * shearMatrix H - F, ?_, ?_⟩
  · refine ⟨adaptedExteriorSpace.sub_mem (hH F hF) hF, ?_⟩
    change upperBlockLinear _ = 0
    rw [map_sub, hupper, sub_self]
  · rw [map_sub, hmixed, add_sub_cancel_right]

theorem formCoordinates_invariantForm :
    formCoordinates invariantForm = Matrix.fromBlocks (0 : HalfMatrix) wallPairing wallPairingᵀ
      ((blockReindex (decodeRows adaptedFormRows)).toBlocks₂₂) := by
  rw [formCoordinates, adaptedBasis, adapted_invariantForm, adaptedForm_blocks]
  rfl

theorem shear_pairing_constraint (H : HalfMatrix)
    (hH : (shearMatrix H)ᵀ * formCoordinates invariantForm * shearMatrix H =
      formCoordinates invariantForm) : (wallPairing * H)ᵀ = wallPairing * H := by
  rw [formCoordinates_invariantForm, shear_pullback] at hH
  have he := congrArg Matrix.toBlocks₂₂ hH
  simp only [Matrix.toBlocks_fromBlocks₂₂, mul_zero, zero_add, wallPairing_transpose] at he
  have hz : wallPairing * H + Hᵀ * wallPairing = 0 := by
    apply add_right_cancel (b := (blockReindex (decodeRows adaptedFormRows)).toBlocks₂₂)
    simpa only [add_assoc, zero_add] using he
  have h : wallPairing * H = Hᵀ * wallPairing := by
    simpa only [ZModModule.neg_eq_self] using (eq_neg_iff_add_eq_zero.mpr hz)
  rw [transpose_mul, wallPairing_transpose]
  exact h.symm

/-- Restrictions to the first 56 adapted coordinates of all exterior forms. -/
def restrictionSpace : Submodule (ZMod 2) HalfMatrix :=
  adaptedExteriorSpace.map upperBlockLinear

/-- Shear terms do not affect the restriction of a pulled-back form. -/
theorem triangular_pullback_upper (G H : HalfMatrix) (F : BlockMatrix) :
    upperBlockLinear ((Matrix.fromBlocks G H 0 G)ᵀ * F * Matrix.fromBlocks G H 0 G) =
      Gᵀ * upperBlockLinear F * G := by
  change ((Matrix.fromBlocks G H 0 G)ᵀ * F * Matrix.fromBlocks G H 0 G).toBlocks₁₁ =
    Gᵀ * F.toBlocks₁₁ * G
  rw [← Matrix.fromBlocks_toBlocks F]
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, transpose_zero,
    mul_zero, zero_mul, add_zero, Matrix.toBlocks_fromBlocks₁₁]

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates
