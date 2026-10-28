module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic

/-!
# Two-groups from faithful triangular binary representations

An invertible triangular matrix over GF(2) has all diagonal entries equal
to one. Cayley–Hamilton makes its difference from the identity nilpotent,
and the characteristic-two power identity gives it two-power order.
Thus any group with a faithful triangular binary representation is a
two-group. No bound on the order of the group is required.

This standard linear-algebra argument is used to control the intrinsic
centralizer in the literal J₄ max4 subgroup, in the verification of
Aschbacher–Smith's condition E (printed pp.3–4 and 481–482).
-/

public section

/-- A faithful representation by unipotent elements in characteristic two
gives two-power order for every group element. -/
theorem IsPGroup.of_injective_unipotent_binary
    {G R : Type*} [Group G] [Ring R] [ExpChar R 2]
    (f : G →* R) (hf : Function.Injective f)
    (hu : ∀ g, IsNilpotent (f g - 1)) : IsPGroup 2 G := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  obtain ⟨n, hn⟩ := hu g
  refine ⟨n, hf ?_⟩
  rw [map_pow, map_one]
  have hz : (f g - 1) ^ 2 ^ n = 0 :=
    pow_eq_zero_of_le (Nat.le_of_lt n.lt_two_pow_self) hn
  have h := add_pow_expChar_pow_of_commute (R := R) 2 n
    (Commute.one_left (f g - 1))
  rw [show 1 + (f g - 1) = f g by rw [add_comm, sub_add_cancel], one_pow, hz,
    add_zero] at h
  exact h

/-- An invertible lower triangular binary matrix is unipotent. -/
theorem Matrix.isNilpotent_sub_one_of_binary_lowerTriangular {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (hM : IsUnit M)
    (ht : ∀ i j, i < j → M i j = 0) : IsNilpotent (M - 1) := by
  have hu : M.transpose.IsUpperTriangular := fun i j hij => ht j i hij
  have hd : ∀ i, M i i = 1 := by
    have hi : IsUnit (M.transpose.det) := by
      rw [Matrix.det_transpose]
      exact hM.map Matrix.detMonoidHom
    rw [Matrix.det_of_isUpperTriangular hu] at hi
    intro i
    have hii : M i i ≠ 0 :=
      fun hz => hi.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hz)
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (M i i) with h | h
    · exact False.elim (hii h)
    · exact h
  have hc : M.charpoly = (Polynomial.X - Polynomial.C 1) ^ n := by
    rw [← Matrix.charpoly_transpose, Matrix.charpoly_of_isUpperTriangular _ hu]
    simp only [Matrix.transpose_apply, hd]
    simp
  refine ⟨n, ?_⟩
  have hh := Matrix.aeval_self_charpoly M
  rw [hc] at hh
  simpa using hh

/-- Faithful lower triangular binary representations detect two-groups. -/
theorem IsPGroup.of_injective_binary_lowerTriangular
    {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (f : G →* Matrix (Fin n) (Fin n) (ZMod 2)) (hf : Function.Injective f)
    (ht : ∀ g i j, i < j → f g i j = 0) : IsPGroup 2 G := by
  let : ExpChar (Matrix (Fin n) (Fin n) (ZMod 2)) 2 :=
    expChar_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (ZMod 2)
        (Matrix (Fin n) (Fin n) (ZMod 2))) 2
  exact .of_injective_unipotent_binary f hf fun g =>
    Matrix.isNilpotent_sub_one_of_binary_lowerTriangular (f g)
      ((Group.isUnit g).map f) (ht g)
