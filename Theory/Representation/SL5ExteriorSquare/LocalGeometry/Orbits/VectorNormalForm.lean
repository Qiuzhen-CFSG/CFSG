module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Bivectors
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Normal forms for binary five-dimensional bivectors

A nonzero coefficient is moved to the first pair by a permutation matrix.
A unit lower triangular change of coordinates then splits off that hyperbolic
plane, leaving an alternating three-by-three block. A second pivot and shear
reduce a nonzero remaining block to one more hyperbolic plane. The resulting
normal forms are exactly e₁∧e₂ and e₁∧e₂ + e₃∧e₄.

All changes of coordinates are genuine determinant-one matrices: the shears
are unit triangular, and an invertible binary scalar is one. The precise
bivector congruence formula and injectivity supplied by `Orbits.Bivectors`
then turn the matrix normal form into an orbit witness for the actual exterior
action. Over F₂, `Orbits.Basic` identifies these nonzero vectors with the
projective points in the source statement.

Source: Aschbacher–Smith, Lemma 12.5.5(2), printed p.819/PDF p.836.
-/

public section

open scoped Matrix
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private theorem binary_nonzero {x : ZMod 2} (hx : x ≠ 0) : x = 1 :=
  (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) x hx

private def congruent (A B : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  ∃ g : Group, g.val * A * g.val.transpose = B

private theorem congruent_refl (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    congruent A A := ⟨1, by simp⟩

private theorem congruent_trans {A B C : Matrix (Fin 5) (Fin 5) (ZMod 2)}
    (h : congruent A B) (h' : congruent B C) : congruent A C := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨k, hk⟩ := h'
  refine ⟨k * g, ?_⟩
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc] using hk

private def permutationMatrix (p : Equiv.Perm (Fin 5)) :
    Matrix (Fin 5) (Fin 5) (ZMod 2) := (1 : Matrix _ _ _).submatrix p id

private theorem permutation_congruence (p : Equiv.Perm (Fin 5))
    (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    permutationMatrix p * A * (permutationMatrix p).transpose = A.submatrix p p := by
  unfold permutationMatrix
  rw [Matrix.transpose_submatrix, Matrix.transpose_one]
  change (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)).submatrix p (Equiv.refl _) * A *
    (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)).submatrix (Equiv.refl _) p = _
  rw [Matrix.one_submatrix_mul _ (Equiv.refl (Fin 5)),
    Matrix.mul_submatrix_one (Equiv.refl (Fin 5))]
  rfl

private def permSL (p : Equiv.Perm (Fin 5)) : Group :=
  ⟨permutationMatrix p, by
    apply binary_nonzero
    have hp : permutationMatrix p * (permutationMatrix p).transpose = 1 := by
      have h := permutation_congruence p 1
      simpa using h
    have h := congrArg Matrix.det hp
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    intro hz
    rw [hz, zero_mul] at h
    exact zero_ne_one h⟩

private theorem perm_congruence (p : Equiv.Perm (Fin 5))
    (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    (permSL p).val * A * (permSL p).val.transpose = A.submatrix p p :=
  permutation_congruence p A

private def pivotPerm (t : Fin 10) : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 (pair t 0) * Equiv.swap 1 (pair t 1)

private theorem pivotPerm_pair (t : Fin 10) :
    pivotPerm t 0 = pair t 0 ∧ pivotPerm t 1 = pair t 1 := by
  fin_cases t <;> decide

private theorem alternatingMatrix_pair (c : Coordinates) (t : Fin 10) :
    alternatingMatrix c (pair t 0) (pair t 1) = c t := by
  fin_cases t <;> rfl

private theorem alternatingMatrix_reindex (p : Equiv.Perm (Fin 5)) (c : Coordinates) :
    alternatingMatrix (fun t => alternatingMatrix c (p (pair t 0)) (p (pair t 1))) =
      (alternatingMatrix c).submatrix p p := by
  -- Reconstruction depends only on symmetry and the zero diagonal.
  have reconstruct (A : Matrix (Fin 5) (Fin 5) (ZMod 2))
      (hd : ∀ i, A i i = 0) (hs : ∀ i j, A i j = A j i) :
      alternatingMatrix (fun t => A (p (pair t 0)) (p (pair t 1))) =
        A.submatrix p p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (hd _).symm | exact hs _ _
  apply reconstruct (alternatingMatrix c) (alternatingMatrix_diagonal c)
  intro i j
  exact congrArg (fun A => A j i) (alternatingMatrix_transpose c)

private def clearFirst (c : Coordinates) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of ![![1,0,0,0,0], ![0,1,0,0,0], ![c 4,c 1,1,0,0],
    ![c 5,c 2,0,1,0], ![c 6,c 3,0,0,1]]

private theorem clearFirst_det (c : Coordinates) : (clearFirst c).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [clearFirst, Fin.prod_univ_succ]
  · intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp_all [clearFirst]

private def residual (a b d : ZMod 2) : Coordinates := ![1,0,0,0,0,0,0,a,b,d]

private theorem clearFirst_congruence (c : Coordinates) (hc : c 0 = 1) :
    clearFirst c * alternatingMatrix c * (clearFirst c).transpose =
      alternatingMatrix (residual
        (c 7 + c 4 * c 2 + c 1 * c 5)
        (c 8 + c 4 * c 3 + c 1 * c 6)
        (c 9 + c 5 * c 3 + c 2 * c 6)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clearFirst, alternatingMatrix, residual, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ, hc] <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      show (6 : ZMod 2) = 0 by decide, mul_zero, mul_one]

private def clearLast (b d : ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of ![![1,0,0,0,0], ![0,1,0,0,0], ![0,0,1,0,0],
    ![0,0,0,1,0], ![0,0,d,b,1]]

private theorem clearLast_det (b d : ZMod 2) : (clearLast b d).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [clearLast, Fin.prod_univ_succ]
  · intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp_all [clearLast]

private theorem clearLast_congruence (b d : ZMod 2) :
    clearLast b d * alternatingMatrix (residual 1 b d) * (clearLast b d).transpose =
      alternatingMatrix (residual 1 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clearLast, alternatingMatrix, residual, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ] <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide,
      show (6 : ZMod 2) = 0 by decide, mul_zero]

private theorem residual_swap_last (a b d : ZMod 2) :
    congruent (alternatingMatrix (residual a b d))
      (alternatingMatrix (residual b a d)) := by
  refine ⟨permSL (Equiv.swap 3 4),
    (perm_congruence (Equiv.swap 3 4) _).trans ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix, Equiv.swap_apply_def, alternatingMatrix, residual]

private theorem residual_swap_outer (a b d : ZMod 2) :
    congruent (alternatingMatrix (residual a b d))
      (alternatingMatrix (residual d b a)) := by
  refine ⟨permSL (Equiv.swap 2 4),
    (perm_congruence (Equiv.swap 2 4) _).trans ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix, Equiv.swap_apply_def, alternatingMatrix, residual]

private theorem residual_normal_form (a b d : ZMod 2) :
    congruent (alternatingMatrix (residual a b d)) (alternatingMatrix (residual 0 0 0)) ∨
      congruent (alternatingMatrix (residual a b d)) (alternatingMatrix (residual 1 0 0)) := by
  have h (b d : ZMod 2) : congruent (alternatingMatrix (residual 1 b d))
      (alternatingMatrix (residual 1 0 0)) :=
    ⟨⟨clearLast b d, clearLast_det b d⟩, clearLast_congruence b d⟩
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      by_cases hd : d = 0
      · subst d
        exact Or.inl (congruent_refl _)
      · rw [binary_nonzero hd]
        exact Or.inr (residual_swap_outer 0 0 1)
    · rw [binary_nonzero hb]
      exact Or.inr (congruent_trans (residual_swap_last 0 1 d) (h 0 d))
  · rw [binary_nonzero ha]
    exact Or.inr (h b d)

private theorem first_pair_normal_form (c : Coordinates) (hc : c 0 = 1) :
    congruent (alternatingMatrix c) (alternatingMatrix (residual 0 0 0)) ∨
      congruent (alternatingMatrix c) (alternatingMatrix (residual 1 0 0)) := by
  have h : congruent (alternatingMatrix c) (alternatingMatrix (residual
      (c 7 + c 4 * c 2 + c 1 * c 5) (c 8 + c 4 * c 3 + c 1 * c 6)
      (c 9 + c 5 * c 3 + c 2 * c 6))) :=
    ⟨⟨clearFirst c, clearFirst_det c⟩, clearFirst_congruence c hc⟩
  exact (residual_normal_form _ _ _).imp (congruent_trans h) (congruent_trans h)

/-- Every nonzero binary alternating five-by-five matrix has one or two
hyperbolic blocks, by an actual determinant-one change of coordinates. -/
theorem alternatingMatrix_normal_form (c : Coordinates) (hc : c ≠ 0) :
    ∃ g : Group,
      g.val * alternatingMatrix c * g.val.transpose =
        alternatingMatrix ![1,0,0,0,0,0,0,0,0,0] ∨
      g.val * alternatingMatrix c * g.val.transpose =
        alternatingMatrix ![1,0,0,0,0,0,0,1,0,0] := by
  obtain ⟨t, ht⟩ : ∃ t, c t ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  let p := pivotPerm t
  let c' : Coordinates := fun s => alternatingMatrix c (p (pair s 0)) (p (pair s 1))
  have hp : congruent (alternatingMatrix c) (alternatingMatrix c') := by
    exact ⟨permSL p, (perm_congruence p _).trans (alternatingMatrix_reindex p c).symm⟩
  have hc' : c' 0 = 1 := by
    change alternatingMatrix c (pivotPerm t 0) (pivotPerm t 1) = 1
    rw [(pivotPerm_pair t).1, (pivotPerm_pair t).2, alternatingMatrix_pair]
    exact binary_nonzero ht
  rcases first_pair_normal_form c' hc' with h | h
  · obtain ⟨g, hg⟩ := congruent_trans hp h
    exact ⟨g, Or.inl hg⟩
  · obtain ⟨g, hg⟩ := congruent_trans hp h
    exact ⟨g, Or.inr hg⟩

/-- The two alternating normal forms are the literal source bivectors. -/
theorem bivector_normal_form (v : V) (hv : v ≠ 0) :
    ∃ g : Group, exteriorAction 2 g v = decomposable ∨
      exteriorAction 2 g v = nondecomposable := by
  have hc : coordinates v ≠ 0 := by
    intro hc
    apply hv
    exact coordinates.injective (hc.trans (map_zero coordinates).symm)
  obtain ⟨g, hg | hg⟩ := alternatingMatrix_normal_form (coordinates v) hc
  · refine ⟨g, Or.inl (bivectorMatrix_injective ?_)⟩
    rw [bivectorMatrix_action]
    simpa only [bivectorMatrix, coordinates_decomposable] using hg
  · refine ⟨g, Or.inr (bivectorMatrix_injective ?_)⟩
    rw [bivectorMatrix_action]
    simpa only [bivectorMatrix, coordinates_nondecomposable] using hg

/-- The two displayed nonzero vectors exhaust the genuine SL₅(2) orbits on
Λ²(F₂⁵). This is the vector form of Aschbacher–Smith 12.5.5(2). -/
theorem exterior_orbits_exhaustive (v : V) (hv : v ≠ 0) :
    InExteriorOrbit decomposable v ∨ InExteriorOrbit nondecomposable v := by
  obtain ⟨g, hg | hg⟩ := bivector_normal_form v hv
  · exact Or.inl (InExteriorOrbit.symm ⟨g, hg⟩)
  · exact Or.inr (InExteriorOrbit.symm ⟨g, hg⟩)

end Representation.SL5ExteriorSquare
