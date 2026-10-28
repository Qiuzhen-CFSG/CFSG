module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.MatrixChecks.Columns

/-!
# Linear interpretation of the checked adjoint flag witnesses

The bounded integer certificates give an invertible adapted basis and both
full matrix intertwining identities. Column bounds then certify the proposed
flag. The separate native comparison must identify `savedGeneratorMatrix`
with the actual sparse block rule before these coordinates are applied to the
M22 action. No simplicity statement is inferred from triangularity.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.MatrixChecks
open InducedFiltration

private theorem bit_power (x y : ℕ) : bit (2 ^ y) x = if y = x then 1 else 0 := by
  simp [bit, Nat.testBit_two_pow]

/-- The saved change of basis is genuinely invertible. -/
theorem basis_mul_inverse : basisMatrix * inverseMatrix = 1 := by
  ext x y
  have h := congrArg (fun v => bit v x.val) (all_columns y).1
  rw [bit_product _ 352 basisColumns_length, bit_power] at h
  simpa only [basisMatrix, inverseMatrix, Matrix.mul_apply, Matrix.one_apply,
    Fin.val_inj, eq_comm] using h

theorem inverse_mul_basis : inverseMatrix * basisMatrix = 1 :=
  (mul_eq_one_comm (a := basisMatrix) (b := inverseMatrix)).mp basis_mul_inverse

/-- All extension blocks are retained in the saved conjugacy identity. -/
theorem basis_mul_action (k : Fin 2) :
    basisMatrix * actionMatrix k = savedGeneratorMatrix k * basisMatrix := by
  ext x y
  have h := congrArg (fun v => bit v x.val) ((all_columns y).2.1 k)
  rw [bit_product _ 352 basisColumns_length,
    bit_product _ 352 (generatorColumns_length k)] at h
  exact h

private theorem cut_eq_full (m : ℕ) (hm : 9 ≤ m) : cut m = 352 := by
  unfold cut
  rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
  rfl

/-- Saved adapted matrices preserve every proposed initial coordinate subspace. -/
theorem upper (m : ℕ) (k : Fin 2) (x y : Fin 352)
    (hx : cut m ≤ x.val) (hy : y.val < cut m) : actionMatrix k x y = 0 := by
  by_cases hm : m < 9
  · have h := (all_columns y).2.2 k ⟨m, hm⟩ hy
    have h' : (actionColumns k)[y.val]! < 2 ^ x.val :=
      h.trans_le (Nat.pow_le_pow_right (by decide) hx)
    change (if (actionColumns k)[y.val]!.testBit x.val then (1 : ZMod 2) else 0) = 0
    rw [Nat.testBit_lt_two_pow h']
    rfl
  · rw [cut_eq_full m (by omega)] at hx
    omega

/-- The certified adapted coordinate equivalence for the saved matrices. -/
def basisCoordinates : Space ≃ₗ[ZMod 2] Space :=
  { inverseMatrix.mulVecLin with
    invFun := basisMatrix.mulVec
    left_inv := fun v => by
      change basisMatrix.mulVec (inverseMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec]
    right_inv := fun v => by
      change inverseMatrix.mulVec (basisMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_basis, Matrix.one_mulVec] }

set_option maxRecDepth 8192 in
theorem basisCoordinates_symm_apply (v : Space) :
    basisCoordinates.symm v = basisMatrix.mulVec v := rfl

theorem basisCoordinates_generator (k : Fin 2) (v : Space) :
    basisCoordinates ((savedGeneratorMatrix k).mulVec v) =
      (actionMatrix k).mulVec (basisCoordinates v) := by
  apply basisCoordinates.symm.injective
  rw [basisCoordinates.symm_apply_apply, basisCoordinates_symm_apply,
    Matrix.mulVec_mulVec, basis_mul_action, ← Matrix.mulVec_mulVec,
    ← basisCoordinates_symm_apply, basisCoordinates.symm_apply_apply]

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.MatrixChecks
