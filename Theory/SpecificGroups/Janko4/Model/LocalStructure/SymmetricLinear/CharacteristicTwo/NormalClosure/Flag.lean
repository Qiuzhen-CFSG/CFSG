module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure.ProgramEvaluation
public import Theory.LinearAlgebra.BinaryTriangularPGroup

/-!
# The invariant flag and its normal two-group kernel

In the certified coordinates, both literal max4 generators preserve the flag
with cumulative dimensions `0,4,16,28,31,34,37,40,72,84,87,90,93,96,108,112`.
Bounds on the 112 packed rows certify all entries above the block diagonal.
Multiplicative closure and finiteness extend this to the generated subgroup.

Taking diagonal blocks is multiplicative on block triangular matrices. Its
kernel is normal and faithfully lower triangular over GF(2), hence a two-group
by `BinaryTriangularPGroup`. `NormalClosure` applies this to the literal seed.
This avoids any premise identifying a quotient or the entire two-core.

The block data and generation argument adapt the saved quotient flag proof;
see `source/README.md`. The application is Aschbacher–Smith condition E,
printed pp.3–4 and 481–482, with A.3.12 on pp.47–48.
-/

public section

set_option Elab.async false

namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure
local notation "ρ" => coordinateHom basis_mul_basisInverse basisInverse_mul_basis

private lemma closure_first_second :
    Subgroup.closure ({first, second} : Set max4Subgroup) = ⊤ := by
  have h : max4Subgroup.subtype ⁻¹' {(max4Program a b).1, (max4Program a b).2} =
      ({first, second} : Set max4Subgroup) := by
    ext g
    change (g.val = first.val ∨ g.val = second.val) ↔ (g = first ∨ g = second)
    simp only [Subtype.val_inj]
  rw [← h]
  exact Subgroup.closure_preimage_eq_top _

/-- Reverse the block order so that `BlockTriangular` means lower triangular
in the row-vector convention used by the source matrices. -/
@[expose] def flagBlock (i : Fin 112) : ℕᵒᵈ := OrderDual.toDual <|
  if i.val < 4 then 0 else
  if i.val < 16 then 1 else
  if i.val < 28 then 2 else
  if i.val < 31 then 3 else
  if i.val < 34 then 4 else
  if i.val < 37 then 5 else
  if i.val < 40 then 6 else
  if i.val < 72 then 7 else
  if i.val < 84 then 8 else
  if i.val < 87 then 9 else
  if i.val < 90 then 10 else
  if i.val < 93 then 11 else
  if i.val < 96 then 12 else
  if i.val < 108 then 13 else 14

/-- The endpoint of the block containing a row. -/
private def flagEnd (i : Fin 112) : ℕ :=
  (#[4,16,28,31,34,37,40,72,84,87,90,93,96,108,112] : Array ℕ)[OrderDual.ofDual (flagBlock i)]!

set_option maxRecDepth 10000 in
private theorem flagEnd_le (i j : Fin 112) : flagBlock j < flagBlock i → flagEnd i ≤ j.val := by
  revert i j
  decide +kernel

private lemma triangular_of_row_bounds (xs : Vector ℕ 112)
    (h : ∀ i : Fin 112, xs.get i < 2 ^ flagEnd i) :
    (decodeRows xs).BlockTriangular flagBlock := by
  intro i j hij
  have he := (h i).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (flagEnd_le i j hij))
  simp [decodeRows, Nat.testBit_lt_two_pow he]

set_option maxRecDepth 10000 in
private theorem first_row_bounds :
    ∀ i : Fin 112, Coordinates.firstRows.get i < 2 ^ flagEnd i := by decide +kernel

set_option maxRecDepth 10000 in
private theorem second_row_bounds :
    ∀ i : Fin 112, Coordinates.secondRows.get i < 2 ^ flagEnd i := by decide +kernel

private theorem first_blockTriangular :
    (decodeRows Coordinates.firstRows).BlockTriangular flagBlock :=
  triangular_of_row_bounds _ first_row_bounds

private theorem second_blockTriangular :
    (decodeRows Coordinates.secondRows).BlockTriangular flagBlock :=
  triangular_of_row_bounds _ second_row_bounds

/-- Every actual element of max4 preserves the certified flag. -/
theorem coordinates_blockTriangular (g : max4Subgroup) :
    (ρ g).BlockTriangular flagBlock := by
  let S : Submonoid max4Subgroup :=
    (Matrix.blockTriangularSubsemiring (ZMod 2) flagBlock).toSubmonoid.comap
      ρ
  have hle : Submonoid.closure ({first, second} : Set max4Subgroup) ≤ S := by
    apply Submonoid.closure_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change (ρ first).BlockTriangular flagBlock
      rw [coordinateHom_apply, first_coordinates]
      exact first_blockTriangular
    · change (ρ second).BlockTriangular flagBlock
      rw [coordinateHom_apply, second_coordinates]
      exact second_blockTriangular
  have htop : Submonoid.closure ({first, second} : Set max4Subgroup) = ⊤ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, closure_first_second]
    rfl
  exact hle (htop ▸ Submonoid.mem_top g)


set_option maxRecDepth 10000 in
private theorem flagBlock_antitone : ∀ i j : Fin 112, i < j → flagBlock j ≤ flagBlock i :=
  by decide +kernel

section General
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Semiring R]
variable {α : Type*} [LinearOrder α] (b : n → α)

private def diagonalPart (M : Matrix n n R) : Matrix n n R :=
  fun i j => if b i = b j then M i j else 0

omit [Fintype n] in
private lemma diagonalPart_one : diagonalPart b (1 : Matrix n n R) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [diagonalPart]
  · simp [diagonalPart, Matrix.one_apply_ne hij]

omit [DecidableEq n] in
private lemma diagonalPart_mul {M N : Matrix n n R}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) :
    diagonalPart b (M * N) = diagonalPart b M * diagonalPart b N := by
  ext i j
  by_cases hij : b i = b j
  · simp only [diagonalPart, hij, if_true, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : b i = b k
    · simp [hik, ← hij]
    · have hkj : b k ≠ b j := by simpa [← hij] using Ne.symm hik
      simp only [hkj, if_false, mul_zero]
      rcases lt_or_gt_of_ne hik with h | h
      · rw [hN (hij ▸ h), mul_zero]
      · rw [hM h, zero_mul]
  · simp only [diagonalPart, hij, if_false, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : b i = b k
    · have hkj : b k ≠ b j := by simpa [hik] using hij
      simp [hkj]
    · simp [hik]
end General

/-- The diagonal-block action of the literal max4 subgroup. -/
def flagDiagonalHom : max4Subgroup →* BinaryMatrix where
  toFun g := diagonalPart flagBlock (ρ g)
  map_one' := by rw [map_one, diagonalPart_one]
  map_mul' g h := by
    rw [map_mul]
    exact diagonalPart_mul _ (coordinates_blockTriangular g) (coordinates_blockTriangular h)

theorem flagDiagonalHom_apply (g : max4Subgroup) (i j : Fin 112) :
    flagDiagonalHom g i j = if flagBlock i = flagBlock j then coordinates g i j else 0 := by
  change (if flagBlock i = flagBlock j then ρ g i j else 0) = _
  rw [coordinateHom_apply]

/-- Its normal kernel has a faithful lower triangular binary representation. -/
theorem flagDiagonalKernel_isPGroup : IsPGroup 2 flagDiagonalHom.ker := by
  apply IsPGroup.of_injective_binary_lowerTriangular ((ρ).comp flagDiagonalHom.ker.subtype)
    ((coordinateHom_injective _ _).comp Subtype.val_injective)
  intro g i j hij
  change ρ (g : max4Subgroup) i j = 0
  rcases lt_or_eq_of_le (flagBlock_antitone i j hij) with h | h
  · exact coordinates_blockTriangular g.val h
  · have hg : diagonalPart flagBlock (ρ (g : max4Subgroup)) = 1 := g.property
    have he := congrFun (congrFun hg i) j
    simpa [diagonalPart, h, Matrix.one_apply_ne (ne_of_lt hij)] using he

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure
