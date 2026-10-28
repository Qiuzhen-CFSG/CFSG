module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.Packed

/-!
# Checked adapted coordinates for the 230-dimensional M23 candidate

The kernel checks a basis inverse and both complete conjugacy identities
using packed binary XOR. The column bounds then prove upper block triangularity
at every cut. These identities retain all extension blocks. Identification
with the native induction and irreducibility of the factors remain separate.

Certificate method adapted from the project's M22 HermitianFiltration.
Source application: Guralnick--Malle I, Proposition 5.1, M23 paragraph.
-/

@[expose] public section
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
namespace MatrixChecks

set_option maxRecDepth 8192 in
private theorem packed_inverse : ∀ (y : Fin 230),
    combineList (basisList) (inverseColumns y) = 2 ^ y.val := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_action : ∀ (j : Fin 2) (y : Fin 230),
    combineList (basisList) (actionColumns j y) =
      combineList (generatorColumnList j) (basis y) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_upper : ∀ (m : Fin 6) (j : Fin 2) (y : Fin 230),
    y.val < cut m.val → actionColumns j y < 2 ^ cut m.val := by
  decide +kernel

theorem basis_mul_inverse : basisMatrix * inverseMatrix = 1 := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_inverse y)
  rw [bit_combineList _ 230 (basisList_length), bit_power] at h
  simpa only [basisMatrix, inverseMatrix, basis, bit, Matrix.mul_apply, Matrix.one_apply,
    Fin.val_inj, eq_comm] using h

theorem inverse_mul_basis : inverseMatrix * basisMatrix = 1 :=
  (mul_eq_one_comm (a := basisMatrix) (b := inverseMatrix)).mp (basis_mul_inverse)

theorem basis_mul_action (j : Fin 2) :
    basisMatrix * actionMatrix j = generatorMatrix j * basisMatrix := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_action j y)
  rw [bit_combineList _ 230 (basisList_length),
    bit_combineList _ 230 (generatorColumnList_length j)] at h
  exact h

theorem cut_eq_full (m : ℕ) (hm : 6 ≤ m) : cut m = 230 := by
  unfold cut
  rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
  rfl

theorem upper (m : ℕ) (j : Fin 2) (x y : Fin 230)
    (hx : cut m ≤ x.val) (hy : y.val < cut m) : actionMatrix j x y = 0 := by
  by_cases hm : m < 6
  · have h := packed_upper ⟨m, hm⟩ j y hy
    have h' : actionColumns j y < 2 ^ x.val :=
      h.trans_le (Nat.pow_le_pow_right (by decide) hx)
    simp [actionMatrix, bit, Nat.testBit_lt_two_pow h']
  · rw [cut_eq_full m (by omega)] at hx
    omega

def basisCoordinates : Space ≃ₗ[ZMod 2] Space :=
  { (inverseMatrix).mulVecLin with
    invFun := (basisMatrix).mulVec
    left_inv := fun v => by
      change (basisMatrix).mulVec ((inverseMatrix).mulVec v) = v
      rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec]
    right_inv := fun v => by
      change (inverseMatrix).mulVec ((basisMatrix).mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_basis, Matrix.one_mulVec] }

set_option maxRecDepth 8192 in
theorem basisCoordinates_symm_apply (v : Space) :
    basisCoordinates.symm v = (basisMatrix).mulVec v := rfl

theorem basisCoordinates_generator (j : Fin 2) (v : Space) :
    basisCoordinates ((generatorMatrix j).mulVec v) =
      (actionMatrix j).mulVec (basisCoordinates v) := by
  have h (w : Space) :
      (basisMatrix).mulVec ((actionMatrix j).mulVec w) =
        (generatorMatrix j).mulVec ((basisMatrix).mulVec w) := by
    simp only [Matrix.mulVec_mulVec, basis_mul_action]
  apply basisCoordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply, basisCoordinates_symm_apply, h,
    ← basisCoordinates_symm_apply, LinearEquiv.symm_apply_apply]

end MatrixChecks
end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
