module

public import Theory.SpecificGroups.UnitaryThree.MatrixGroup

/-!
# Generation of the full unitary matrix group

The root, torus and swap matrices generate all of `UnitaryThree.matrixGroup`.
For a matrix whose first column is `(a,b,c)` with `c ≠ 0`, left multiplication
by the root with parameters `(-b/c, star (a/c))`, followed by the swap, moves
that column to the infinity line. Isotropy supplies the root equation and the
vanishing entries. If `c = 0`, isotropy already forces `b = 0`.

An isometry fixing the infinity line is upper triangular. Its determinant and
column pairings force diagonal entries `(r^5,r^2,r)` and identify it as a root
matrix times a torus matrix. The small scalar identities over F₉ are checked
by kernel reduction; no enumeration of the full matrix group is needed.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section VI; the matrix Bruhat decomposition.
-/

open FiniteField Matrix
open scoped Matrix
namespace UnitaryThree

private theorem diagonal_coordinates : ∀ a d f : Nine,
    star a * f = 1 → a * d * f = 1 →
    a = f ^ 5 ∧ d = f ^ 2 ∧ f ≠ 0 := by decide +kernel

private theorem middle_coordinate : ∀ b e f : Nine,
    f ≠ 0 → star b * f + star (f ^ 2) * e = 0 →
    b = -star (e / f) * f ^ 2 := by decide +kernel

private theorem root_coordinates : ∀ c e f : Nine,
    f ≠ 0 → star c * f + star e * e + star f * c = 0 →
    c / f + star (c / f) + star (e / f) * (e / f) = 0 := by decide +kernel

private theorem normalize_coordinates : ∀ a b c : Nine,
    c ≠ 0 → star a * c + star b * b + star c * a = 0 →
    star (a / c) + star (star (a / c)) + star (-b / c) * (-b / c) = 0 ∧
    a - star (-b / c) * b + star (a / c) * c = 0 ∧ b + (-b / c) * c = 0 := by
  decide +kernel


private theorem pairing (A : matrixGroup) (i j : Fin 3) :
    star (A.val.val 0 i) * A.val.val 2 j +
      star (A.val.val 1 i) * A.val.val 1 j +
      star (A.val.val 2 i) * A.val.val 0 j = gram i j := by
  have h := congrFun (congrFun A.property i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply] at h
  simpa [gram, add_comm, add_left_comm, add_assoc] using h

private theorem triangular_factor (A : matrixGroup)
    (h10 : A.val.val 1 0 = 0) (h20 : A.val.val 2 0 = 0) :
    ∃ p : Root, ∃ r : Nineˣ, A = matrixRoot p * matrixTorus r := by
  have h02 := pairing A 0 2
  have h01 := pairing A 0 1
  simp only [h10, h20, star_zero, zero_mul, add_zero] at h02 h01
  change _ = 1 at h02
  change _ = 0 at h01
  have ha : A.val.val 0 0 ≠ 0 := by
    intro hz
    simp [hz] at h02
  have h21 : A.val.val 2 1 = 0 := (mul_eq_zero.mp h01).resolve_left (by
    simpa using ha)
  have hd := A.val.property
  simp only [Matrix.det_fin_three, h10, h20, h21, mul_zero, zero_mul,
    add_zero, sub_zero] at hd
  obtain ⟨h00, h11, h22⟩ := diagonal_coordinates _ _ _ h02 hd
  have h12 := pairing A 1 2
  simp only [h21, star_zero, zero_mul, add_zero, h11] at h12
  change star (A.val.val 0 1) * A.val.val 2 2 +
    star (A.val.val 2 2 ^ 2) * A.val.val 1 2 = 0 at h12
  have h01' := middle_coordinate _ _ _ h22 h12
  have h22' := pairing A 2 2
  change _ = 0 at h22'
  let p : Root := ⟨(A.val.val 1 2 / A.val.val 2 2, A.val.val 0 2 / A.val.val 2 2),
    root_coordinates _ _ _ h22 h22'⟩
  let r : Nineˣ := Units.mk0 (A.val.val 2 2) h22
  refine ⟨p, r, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change A.val.val = (rootMatrix p).val * (torusMatrix r).val
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, torusMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, p, r, h00, h11, h01', h10, h20, h21, h22]

/-- The root, torus and swap matrices generate every determinant-one isometry. -/
public theorem matrixGroup_generated :
    Subgroup.closure (Set.range matrixRoot ∪ Set.range matrixTorus ∪ {matrixSwap}) = ⊤ := by
  let H := Subgroup.closure (Set.range matrixRoot ∪ Set.range matrixTorus ∪ {matrixSwap})
  have hr (p : Root) : matrixRoot p ∈ H :=
    Subgroup.subset_closure (Or.inl (Or.inl ⟨p, rfl⟩))
  have ht (r : Nineˣ) : matrixTorus r ∈ H :=
    Subgroup.subset_closure (Or.inl (Or.inr ⟨r, rfl⟩))
  have hs : matrixSwap ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have htri (A : matrixGroup) (h10 : A.val.val 1 0 = 0) (h20 : A.val.val 2 0 = 0) :
      A ∈ H := by
    obtain ⟨p, r, rfl⟩ := triangular_factor A h10 h20
    exact H.mul_mem (hr p) (ht r)
  apply (Subgroup.eq_top_iff' _).mpr
  intro A
  change A ∈ H
  have hi := pairing A 0 0
  change _ = 0 at hi
  by_cases hc : A.val.val 2 0 = 0
  · have hb : A.val.val 1 0 = 0 := by
      simpa only [hc, mul_zero, star_zero, zero_mul, zero_add, add_zero,
        mul_eq_zero, star_eq_zero, or_self] using hi
    exact htri A hb hc
  · obtain ⟨hp, htop, hmid⟩ := normalize_coordinates _ _ _ hc hi
    let p : Root := ⟨(-A.val.val 1 0 / A.val.val 2 0,
      star (A.val.val 0 0 / A.val.val 2 0)), hp⟩
    have h10 : (matrixSwap * matrixRoot p * A).val.val 1 0 = 0 := by
      change (-gram * (rootMatrix p).val * A.val.val) 1 0 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_succ, gram, rootMatrix, p]
      linear_combination -hmid
    have h20 : (matrixSwap * matrixRoot p * A).val.val 2 0 = 0 := by
      change (-gram * (rootMatrix p).val * A.val.val) 2 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_three, gram, rootMatrix, p,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Matrix.neg_apply, neg_mul, zero_mul,
        one_mul, add_zero, neg_neg]
      linear_combination -htop
    have hm := H.mul_mem (H.inv_mem (H.mul_mem hs (hr p)))
      (htri (matrixSwap * matrixRoot p * A) h10 h20)
    simpa only [inv_mul_cancel_left] using hm

end UnitaryThree
