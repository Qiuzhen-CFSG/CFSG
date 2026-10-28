module

public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore.Diagonal
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
/-!
# The normal diagonal sign subgroup of the unitary monomial group

Inside the actual determinant-one monomial group, the diagonal matrices
whose square is one form the diagonal sign subgroup. Conjugation by a
monomial matrix preserves diagonality: a column of its inverse is supported
on one coordinate, and multiplying by a diagonal matrix preserves that support.
The square equation is also preserved, so this two-subgroup is normal.

For identity Gram matrix the three diagonal matrices with one entry `1` and
two entries `-1` belong to this subgroup. Commuting with these signs forces
every off-diagonal entry to equal its negative. Thus in characteristic different
from two the centralizer consists of diagonal matrices.

Source: the decomposition stabilizer in GLS3, Theorem 6.5.3(b),
`refs/KGroup/GLS3/chapter6.tex`, used in Aschbacher–Smith, Proposition 1.3.4,
printed p.511 (PDF p.528). This proves the concrete sign-subgroup input to the
local core calculation, independently of a coordinate-permutation action.
-/

public section

open scoped Pointwise
open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial

variable {E : Type*} [Field E] {J : HermitianForm 3 E}

private theorem column_axis (g : special J) (j : Fin 3) :
    ∃ k : Fin 3, g.val.val.val k j ≠ 0 ∧ ∀ i : Fin 3, i ≠ k → g.val.val.val i j = 0 := by
  have hg : g.val.val • coordinateVectors (E := E) = coordinateVectors := g.property
  have h := Set.smul_mem_smul_set (a := g.val.val)
    (single_mem_coordinateVectors (E := E) j one_ne_zero)
  rw [hg] at h
  change Matrix.mulVec g.val.val.val (Pi.single j 1) ∈ coordinateVectors at h
  simpa only [Matrix.mulVec_single_one, coordinateVectors, Set.mem_ofPred_eq,
    Matrix.col_apply] using h

private theorem diagonal_conjugate (g x : special J) (hx : IsDiagonal x) :
    IsDiagonal (g * x * g⁻¹) := by
  intro i j hij
  obtain ⟨k, hne, hk⟩ := column_axis g⁻¹ j
  have hs (A : Matrix (Fin 3) (Fin 3) E) :
      (A * (g⁻¹).val.val.val) i j = A i k * (g⁻¹).val.val.val k j := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_single k (fun l _ hl => by rw [hk l hl, mul_zero]) (by simp)
  -- The identity g * g⁻¹ forces the k-th column of g to vanish away from j.
  have hz : g.val.val.val i k = 0 := by
    have h : (g.val.val.val * (g⁻¹).val.val.val) i j = 0 := by
      have hm : g.val.val.val * (g⁻¹).val.val.val = 1 := Units.mul_inv g.val.val
      rw [hm, Matrix.one_apply_ne hij]
    rw [hs] at h
    exact (mul_eq_zero.mp h).resolve_right hne
  change (g.val.val.val * x.val.val.val * (g⁻¹).val.val.val) i j = 0
  rw [hs, ← (show Matrix.IsDiag x.val.val.val from hx).diagonal_diag,
    Matrix.mul_diagonal, hz, zero_mul, zero_mul]

/-- Diagonal involutions (including the identity) inside the determinant-one group. -/
private def signSubgroup (J : HermitianForm 3 E) : Subgroup (special J) where
  carrier := {x | IsDiagonal x ∧ x ^ 2 = 1}
  one_mem' := ⟨Matrix.isDiag_one, one_pow 2⟩
  mul_mem' := by
    rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
    refine ⟨?_, ?_⟩
    · change Matrix.IsDiag (x.val.val.val * y.val.val.val)
      rw [← (show Matrix.IsDiag x.val.val.val from hx).diagonal_diag,
        ← (show Matrix.IsDiag y.val.val.val from hy).diagonal_diag,
        Matrix.diagonal_mul_diagonal]
      exact Matrix.isDiag_diagonal _
    · rw [(commute_of_isDiagonal hx hy).mul_pow, hx2, hy2, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    have hi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hx2)
    rw [hi]
    exact ⟨hx, hx2⟩

private theorem signSubgroup_normal : (signSubgroup J).Normal := by
  refine ⟨?_⟩
  intro x hx g
  refine ⟨diagonal_conjugate g x hx.1, ?_⟩
  change (MulAut.conj g x) ^ 2 = 1
  rw [← map_pow, hx.2, map_one]

private theorem signSubgroup_two : IsPGroup 2 (signSubgroup J) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  exact x.property.2

/-- The sign with its unique positive diagonal entry in coordinate i. -/
private def signMatrix (i : Fin 3) : Matrix (Fin 3) (Fin 3) E :=
  Matrix.diagonal fun k => if k = i then 1 else -1

private theorem signMatrix_sq (i : Fin 3) :
    signMatrix (E := E) i * signMatrix i = 1 := by
  rw [signMatrix, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 1
  congr 1
  funext k
  split_ifs <;> simp

private def signGL (i : Fin 3) : GL (Fin 3) E where
  val := signMatrix i
  inv := signMatrix i
  val_inv := signMatrix_sq i
  inv_val := signMatrix_sq i

private theorem signGL_sq (i : Fin 3) : signGL (E := E) i * signGL i = 1 :=
  Units.ext (signMatrix_sq i)

private def signSU (J : HermitianForm 3 E) (hJ : J.form = 1) (i : Fin 3) :
    J.specialSubgroup := ⟨signGL i, by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · change J.conjTranspose (signMatrix i) * J.form * signMatrix i = J.form
    have hadj : J.conjTranspose (signMatrix i) = signMatrix i := by
      ext k l
      by_cases h : k = l
      · subst l
        by_cases hki : k = i <;> simp [signMatrix, HermitianForm.conjTranspose, hki]
      · simp [signMatrix, HermitianForm.conjTranspose, h, Ne.symm h]
    rw [hJ, mul_one, hadj, signMatrix_sq]
  · apply Units.ext
    change (signMatrix (E := E) i).det = 1
    fin_cases i <;> simp [signMatrix, Matrix.det_diagonal, Fin.prod_univ_three]⟩

private theorem signGL_preserves (i : Fin 3) {v : Fin 3 → E}
    (hv : v ∈ coordinateVectors) : signGL (E := E) i • v ∈ coordinateVectors := by
  obtain ⟨k, hne, hk⟩ := hv
  change (Matrix.diagonal (fun k => if k = i then (1 : E) else -1)) *ᵥ v ∈ coordinateVectors
  refine ⟨k, ?_, ?_⟩
  · rw [Matrix.mulVec_diagonal]
    split_ifs <;> simpa using hne
  · intro l hl
    rw [Matrix.mulVec_diagonal, hk l hl, mul_zero]

private def signMonomial (J : HermitianForm 3 E) (hJ : J.form = 1) (i : Fin 3) :
    special J := ⟨signSU J hJ i, by
  change signGL i • coordinateVectors (E := E) = coordinateVectors
  apply Set.Subset.antisymm
  · rintro v ⟨w, hw, rfl⟩
    exact signGL_preserves i hw
  · intro v hv
    refine Set.mem_smul_set.mpr ⟨signGL i • v, signGL_preserves i hv, ?_⟩
    rw [smul_smul, signGL_sq, one_smul]⟩

private theorem signMonomial_mem (J : HermitianForm 3 E) (hJ : J.form = 1)
    (i : Fin 3) : signMonomial J hJ i ∈ signSubgroup J := by
  refine ⟨Matrix.isDiag_diagonal _, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change signGL i ^ 2 = 1
  rw [pow_two, signGL_sq]

private theorem signSubgroup_centralizer (J : HermitianForm 3 E) (hJ : J.form = 1)
    (h2 : (2 : E) ≠ 0) (x : special J)
    (hx : x ∈ Subgroup.centralizer (signSubgroup J : Set (special J))) : IsDiagonal x := by
  intro i j hij
  have h := Subgroup.mem_centralizer_iff.mp hx (signMonomial J hJ i)
    (signMonomial_mem J hJ i)
  have hm := congrArg (fun g : special J => g.val.val.val i j) h
  change (signMatrix (E := E) i * x.val.val.val) i j =
    (x.val.val.val * signMatrix (E := E) i) i j at hm
  simp [signMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, Ne.symm hij] at hm
  have hz : (2 : E) * x.val.val.val i j = 0 := by linear_combination hm
  exact (mul_eq_zero.mp hz).resolve_left h2

/-- The actual monomial group has a normal diagonal sign two-subgroup whose
centralizer consists of diagonal matrices. Normality is relative to `special J`. -/
theorem exists_normal_sign_subgroup [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = 1) (h2 : (2 : E) ≠ 0) :
    ∃ V : Subgroup (special J), V.Normal ∧ IsPGroup 2 V ∧
      ∀ x ∈ Subgroup.centralizer (V : Set (special J)), IsDiagonal x := by
  exact ⟨signSubgroup J, signSubgroup_normal, signSubgroup_two,
    signSubgroup_centralizer J hJ h2⟩

end BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial
