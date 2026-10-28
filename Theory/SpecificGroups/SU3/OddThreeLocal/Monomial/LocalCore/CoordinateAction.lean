module

public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore.Diagonal

/-!
# The coordinate action of the actual unitary monomial subgroup

A matrix preserving the punctured coordinate axes has exactly one nonzero
entry in each column. Its row index defines the image of that coordinate.
Matrix multiplication composes these indices, and the inverse matrix provides
the inverse permutation. The permutation fixes every coordinate exactly when
the original matrix is diagonal. Neither finiteness of the field nor a
particular Gram matrix is needed for this construction.

This is the coordinate-action ingredient of the decomposition stabilizer in
GLS3, Theorem 6.5.3(b), `refs/KGroup/GLS3/chapter6.tex`, used in the unitary
case of Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528).
-/

open scoped Pointwise
open Matrix

namespace BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial

variable {E : Type*} [Field E] {J : HermitianForm 3 E}

private theorem column_support (x : special J) (i : Fin 3) :
    ∃ j : Fin 3, x.val.val.val j i ≠ 0 ∧
      ∀ k : Fin 3, k ≠ j → x.val.val.val k i = 0 := by
  have hx : x.val.val • coordinateVectors (E := E) = coordinateVectors :=
    MulAction.mem_stabilizer_iff.mp x.property
  have hi := Set.smul_mem_smul_set (a := x.val.val)
    (single_mem_coordinateVectors i (one_ne_zero : (1 : E) ≠ 0))
  rw [hx] at hi
  change x.val.val.val *ᵥ Pi.single i 1 ∈ coordinateVectors at hi
  simpa only [Matrix.mulVec_single_one, coordinateVectors, Matrix.col_apply,
    Set.mem_ofPred_eq] using hi

private noncomputable def columnIndex (x : special J) (i : Fin 3) : Fin 3 :=
  (column_support x i).choose

private theorem columnIndex_spec (x : special J) (i : Fin 3) :
    x.val.val.val (columnIndex x i) i ≠ 0 ∧
      ∀ k : Fin 3, k ≠ columnIndex x i → x.val.val.val k i = 0 :=
  (column_support x i).choose_spec

private theorem columnIndex_eq_of_ne_zero (x : special J) (i j : Fin 3)
    (h : x.val.val.val j i ≠ 0) : columnIndex x i = j := by
  by_contra hne
  exact h ((columnIndex_spec x i).2 j (Ne.symm hne))

private theorem columnIndex_one (i : Fin 3) : columnIndex (1 : special J) i = i := by
  apply columnIndex_eq_of_ne_zero
  change (1 : Matrix (Fin 3) (Fin 3) E) i i ≠ 0
  simp

private theorem mul_entry (x y : special J) (k i : Fin 3) :
    (x * y).val.val.val k i =
      x.val.val.val k (columnIndex y i) * y.val.val.val (columnIndex y i) i := by
  change (x.val.val.val * y.val.val.val) k i = _
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single (columnIndex y i)
  · intro j _ hj
    rw [(columnIndex_spec y i).2 j hj, mul_zero]
  · simp

private theorem columnIndex_mul (x y : special J) (i : Fin 3) :
    columnIndex (x * y) i = columnIndex x (columnIndex y i) := by
  apply columnIndex_eq_of_ne_zero
  rw [mul_entry]
  exact mul_ne_zero (columnIndex_spec x (columnIndex y i)).1 (columnIndex_spec y i).1

private noncomputable def coordinatePermutation (x : special J) : Equiv.Perm (Fin 3) where
  toFun := columnIndex x
  invFun := columnIndex x⁻¹
  left_inv i := by rw [← columnIndex_mul, inv_mul_cancel, columnIndex_one]
  right_inv i := by rw [← columnIndex_mul, mul_inv_cancel, columnIndex_one]

private noncomputable def coordinateAction : special J →* Equiv.Perm (Fin 3) where
  toFun := coordinatePermutation
  map_one' := Equiv.ext columnIndex_one
  map_mul' x y := Equiv.ext (columnIndex_mul x y)

/-- The actual monomial subgroup permutes the three coordinate axes, with
kernel exactly the matrices whose underlying matrix is diagonal. -/
public theorem exists_coordinate_action (J : HermitianForm 3 E) :
    ∃ f : special J →* Equiv.Perm (Fin 3),
      ∀ x : special J, f x = 1 ↔ IsDiagonal x := by
  refine ⟨coordinateAction, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    have hfix (i : Fin 3) : columnIndex x i = i :=
      congrArg (fun p : Equiv.Perm (Fin 3) => p i) hx
    intro i j hij
    exact (columnIndex_spec x j).2 i (by simpa only [hfix] using hij)
  · intro hx
    apply Equiv.ext
    intro i
    change columnIndex x i = i
    by_contra hne
    exact (columnIndex_spec x i).1 (hx hne)

end BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial
