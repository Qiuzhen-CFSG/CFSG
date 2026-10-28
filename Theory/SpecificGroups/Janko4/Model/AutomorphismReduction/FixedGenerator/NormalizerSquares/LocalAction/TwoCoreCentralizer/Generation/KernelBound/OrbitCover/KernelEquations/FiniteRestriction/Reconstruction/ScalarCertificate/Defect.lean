module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Arithmetic

/-!
# Evaluation of the scalar chart defect

The zeroth defect coordinate is a fixed linear functional on the ambient
module. Its packed row, the first column of every affine direction, and its
embedded image are checked against the published chart. Binary parity then
evaluates the defect on all 124 directions.

Source and matrix conventions: ScalarCertificate/source/README.md.
-/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

private instance defectFinForall {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := Nat.decidableForallFin P

private instance defectScalarEq (x y : ZMod 2) : Decidable (x = y) := ZMod.decidableEq 2 x y

private theorem binaryColumn_rowProduct {n : ℕ} (x : ℕ) (rows : Vector ℕ n) :
    binaryColumn (rowProduct x rows) =
      ∑ i : Fin n, bit x i.val • binaryColumn (rows.get i) := by
  ext j
  change bit (rowProduct x rows) j.val = _
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases h : x.testBit i.val <;> simp [bit, h, binaryColumn]

private theorem inclusion_columns : ∀ i : Fin 112, ∀ j : Fin 50,
    restrictionEmbedding i j = binaryColumn (restrictionColumns.get j) i := by
  intro i j
  rfl

private theorem direction_first_columns : ∀ k : Fin 124, ∀ i : Fin 50,
    affineDirection k i 0 = bit (directionFirstColumns.get k) i.val := by decide +kernel

private theorem packed_direction_images : ∀ k : Fin 124,
    rowProduct (directionFirstColumns.get k) restrictionColumns = directionImages.get k := by
  decide +kernel

private theorem baseImage_direction (k : Fin 124) :
    baseImage (affineDirection k) = binaryColumn (directionImages.get k) := by
  rw [← packed_direction_images k, binaryColumn_rowProduct]
  ext i
  change (restrictionEmbedding *ᵥ (affineDirection k *ᵥ Pi.single 0 1)) i = _
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [inclusion_columns, Matrix.col_apply, direction_first_columns]
  exact mul_comm _ _


/-- The row evaluating the zeroth coordinate of the linear chart defect. -/
private def scalarRow : NaturalModule :=
  Pi.single 0 1 - ∑ i : Fin 22, basisVector i 0 • binaryColumn (dualRows.get i)

private theorem scalarRow_apply (v : NaturalModule) :
    scalarRow ⬝ᵥ v = chartDefect v defectCoordinate := by
  rw [scalarRow, sub_dotProduct, sum_dotProduct]
  simp only [single_dotProduct, one_mul, smul_dotProduct, smul_eq_mul,
    chartDefect_apply, Pi.sub_apply, synthesize, Finset.sum_apply, Pi.smul_apply,
    coordinates, defectCoordinate]
  apply congrArg (fun z : ZMod 2 => v 0 - z)
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private theorem scalarRow_decode :
    scalarRow = binaryColumn 4274206636792214179380280441176065 := by
  exact funext (show ∀ i : Fin 112,
    scalarRow i = binaryColumn 4274206636792214179380280441176065 i from by decide +kernel)

private theorem column_dot (x y : ℕ) (h : x < 2 ^ 112) :
    binaryColumn x ⬝ᵥ binaryColumn y = bit (foldParity 7 (x &&& y)) 0 := by
  rw [parity_sum _ ((Nat.and_le_left).trans_lt h) (show 112 ≤ 2 ^ 7 by decide)]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  change bit x i.val * bit y i.val = bit (x &&& y) i.val
  simp only [bit, Nat.testBit_and]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide

private theorem scalar_coefficients : ∀ k : Fin 124,
    binaryColumn 4274206636792214179380280441176065 ⬝ᵥ binaryColumn (directionImages.get k) =
      bit 17552799707978362774193210816690218843 k.val := by
  simp only [column_dot _ _ (show 4274206636792214179380280441176065 < 2 ^ 112 by decide)]
  decide +kernel

theorem defectScalar_direction (k : Fin 124) :
    defectScalar (affineDirection k) =
      bit 17552799707978362774193210816690218843 k.val := by
  unfold defectScalar
  rw [baseImage_direction, ← scalarRow_apply, scalarRow_decode]
  exact scalar_coefficients k

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

