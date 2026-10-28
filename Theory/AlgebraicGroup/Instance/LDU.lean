module

public import Theory.AlgebraicGroup.Instance.LowerTriangular
public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.Morphism.Operations
public import Theory.AlgebraicGroup.Variety.PrincipalOpen
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Finite Gaussian LDU factorization and the matrix big cell.

For a square matrix over a field, multiplication of a lower-unitriangular
matrix, an invertible diagonal matrix, and an upper-unitriangular matrix is
injective, and its range consists exactly of matrices whose nonempty leading
principal minors are nonzero.  Existence is proved recursively by splitting
off the final row and column and applying the Schur-complement factorization;
the final pivot is nonzero because the determinant is the determinant of the
previous leading block times the Schur complement.

The diagonal pivots are quotients of consecutive leading principal minors.
Replacing the final row or column of a leading block gives bordered-minor
(Cramer's-rule) formulas for every lower or upper factor entry.  These formulas
are the algebraic input used to make the inverse factorization regular on the
associated principal open.  The construction is the standard finite-matrix
Gaussian elimination argument, using Mathlib's block-matrix and Schur-complement
identities and the triangular matrix APIs from `LowerTriangular` and `U`.

The final `GLₙ` section represents the leading minors by explicit coordinate
polynomials, making the Gaussian range a directly exhibited finite principal
open and exposing the inverse-coordinate formulas on that open.  The carrier
varieties are also assembled into a natural polynomial `lduMorphism` by
composing their maps to `GLₙ` with ambient multiplication.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

@[expose]
public def leadingPrincipalSubmatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (r : ℕ) (hr : r ≤ n) : Matrix (Fin r) (Fin r) k :=
  A.submatrix (Fin.castLE hr) (Fin.castLE hr)

@[expose]
public def leadingPrincipalMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (r : ℕ) (hr : r ≤ n) : k :=
  (leadingPrincipalSubmatrix A r hr).det

@[expose]
public def HasNonzeroLeadingPrincipalMinors {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ r (hr : r ≤ n), 0 < r → leadingPrincipalMinor A r hr ≠ 0

/-- Replace the last row of the leading `(j+1)`-by-`(j+1)` block by row `i`. -/
@[expose]
public def lowerBorderRow {n : ℕ} (i j : Fin n) : Fin (j.val + 1) → Fin n := fun r =>
  if hr : r.val < j.val then ⟨r.val, hr.trans j.isLt⟩ else i

/-- Replace the last column of the leading `(i+1)`-by-`(i+1)` block by column `j`. -/
@[expose]
public def upperBorderColumn {n : ℕ} (i j : Fin n) : Fin (i.val + 1) → Fin n := fun c =>
  if hc : c.val < i.val then ⟨c.val, hc.trans i.isLt⟩ else j

/-- The bordered leading minor that recovers a lower-triangular entry. -/
@[expose]
public def lowerBorderedMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) : k :=
  (A.submatrix (lowerBorderRow i j)
    (Fin.castLE (Nat.succ_le_iff.mpr j.isLt))).det

/-- The bordered leading minor that recovers an upper-triangular entry. -/
@[expose]
public def upperBorderedMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) : k :=
  (A.submatrix (Fin.castLE (Nat.succ_le_iff.mpr i.isLt))
    (upperBorderColumn i j)).det

public structure LDUFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) k) where
  lower : Matrix (Fin n) (Fin n) k
  diagonal : Fin n → k
  upper : Matrix (Fin n) (Fin n) k
  lower_unitriangular : lUnipotent n lower
  diagonal_ne_zero : ∀ i, diagonal i ≠ 0
  upper_unitriangular : uUnipotent n upper
  eq_matrix : A = lower * Matrix.diagonal diagonal * upper

/-- The three factors on which Gaussian multiplication is defined. -/
public structure LDUFactors (n : ℕ) where
  lower : Matrix (Fin n) (Fin n) k
  diagonal : Fin n → k
  upper : Matrix (Fin n) (Fin n) k
  lower_unitriangular : lUnipotent n lower
  diagonal_ne_zero : ∀ i, diagonal i ≠ 0
  upper_unitriangular : uUnipotent n upper

@[ext]
public theorem LDUFactors.ext {n : ℕ} {F G : LDUFactors (k := k) n}
    (hlower : F.lower = G.lower) (hdiagonal : F.diagonal = G.diagonal)
    (hupper : F.upper = G.upper) : F = G := by
  cases F
  cases G
  simp_all

/-- Multiplication of lower-unitriangular, invertible-diagonal, and
upper-unitriangular factors. -/
@[expose]
public def LDUFactors.multiply {n : ℕ} (F : LDUFactors (k := k) n) :
    Matrix (Fin n) (Fin n) k :=
  F.lower * Matrix.diagonal F.diagonal * F.upper

@[expose]
public def LDUFactors.factorization {n : ℕ} (F : LDUFactors (k := k) n) :
    LDUFactorization F.multiply where
  lower := F.lower
  diagonal := F.diagonal
  upper := F.upper
  lower_unitriangular := F.lower_unitriangular
  diagonal_ne_zero := F.diagonal_ne_zero
  upper_unitriangular := F.upper_unitriangular
  eq_matrix := rfl

section LDUVarietyMorphism

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def lFactorGLMorphism (n : ℕ) :
    Variety.Morphism (lVariety k n) (glVariety n : Variety k) where
  toFun := fun x => (glPointEquiv n).symm
    (Matrix.GeneralLinearGroup.mk'' (lPointMatrix n x) (lPoint_det_isUnit n x))
  regular := by
    intro c
    rcases c with ⟨i, j⟩ | ⟨⟩
    · refine ⟨MvPolynomial.X (ULift.up (i, j)), ?_⟩
      intro x
      change lPointMatrix n x i j = _
      simp [lPointMatrix, evalPolynomial]
    · refine ⟨MvPolynomial.C 1, ?_⟩
      intro x
      change (lPointMatrix n x).det⁻¹ = _
      rw [lTriangular_det n (lPoint_lUnipotent n x).1]
      simp [(lPoint_lUnipotent n x).2, evalPolynomial]

@[expose]
public noncomputable def uFactorGLMorphism (n : ℕ) :
    Variety.Morphism (uVariety k n) (glVariety n : Variety k) where
  toFun := fun x => (glPointEquiv n).symm
    (Matrix.GeneralLinearGroup.mk'' (uPointMatrix n x) (uPoint_det_isUnit n x))
  regular := by
    intro c
    rcases c with ⟨i, j⟩ | ⟨⟩
    · refine ⟨MvPolynomial.X (ULift.up (i, j)), ?_⟩
      intro x
      change uPointMatrix n x i j = _
      simp [uPointMatrix, evalPolynomial]
    · refine ⟨MvPolynomial.C 1, ?_⟩
      intro x
      change (uPointMatrix n x).det⁻¹ = _
      rw [det_eq_one_of_uUnipotent n (uPoint_uUnipotent n x)]
      simp [evalPolynomial]

@[expose]
public noncomputable def dFactorGLMorphism (n : ℕ) :
    Variety.Morphism (dVariety k n) (glVariety n : Variety k) where
  toFun := fun x => (glPointEquiv n).symm
    (Matrix.GeneralLinearGroup.mk''
      (Matrix.diagonal fun i => dPointEntry n x i)
      (by
        rw [Matrix.det_diagonal]
        exact isUnit_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun i _ =>
          (dPoint_entry_isUnit n x i).ne_zero))
  regular := by
    intro c
    rcases c with ⟨i, j⟩ | ⟨⟩
    · by_cases hij : i = j
      · subst j
        refine ⟨MvPolynomial.X (Sum.inl (ULift.up i)), ?_⟩
        intro x
        change (Matrix.diagonal fun a => dPointEntry n x a) i i = _
        simp [dPointEntry, evalPolynomial]
      · refine ⟨0, ?_⟩
        intro x
        change (Matrix.diagonal fun a => dPointEntry n x a) i j = _
        simp [hij, evalPolynomial]
    · refine ⟨∏ i : Fin n, MvPolynomial.X (Sum.inr (ULift.up i)), ?_⟩
      intro x
      change (Matrix.diagonal fun i => dPointEntry n x i).det⁻¹ = _
      rw [Matrix.det_diagonal, ← Finset.prod_inv_distrib]
      simp [dPoint_entry_inv, dPointEntryInv, evalPolynomial]

/-- The multiplication morphism from lower, diagonal, and upper carriers to
`GLₙ`, with the factors ordered as `L · D · U`. -/
@[expose]
public noncomputable def lduMorphism (n : ℕ) :
    Variety.Morphism
      (Variety.prod (Variety.prod (lVariety k n) (dVariety k n)) (uVariety k n))
      (glVariety n : Variety k) :=
  let LD := Variety.prod (lVariety k n) (dVariety k n)
  let S := Variety.prod LD (uVariety k n)
  let l : Variety.Morphism S (glVariety n : Variety k) :=
    (lFactorGLMorphism n).comp
      ((Variety.Morphism.fst (lVariety k n) (dVariety k n)).comp
        (Variety.Morphism.fst LD (uVariety k n)))
  let d : Variety.Morphism S (glVariety n : Variety k) :=
    (dFactorGLMorphism n).comp
      ((Variety.Morphism.snd (lVariety k n) (dVariety k n)).comp
        (Variety.Morphism.fst LD (uVariety k n)))
  let u : Variety.Morphism S (glVariety n : Variety k) :=
    (uFactorGLMorphism n).comp (Variety.Morphism.snd LD (uVariety k n))
  (AlgebraicGroup.mulMorphism (glVariety n : Variety k)).comp
    (((AlgebraicGroup.mulMorphism (glVariety n : Variety k)).comp (l.pair d)).pair u)

end LDUVarietyMorphism

private lemma submatrix_mul_of_uTriangular_right
    {n r m : ℕ} (hr : r ≤ n) (rows : Fin m → Fin n)
    {M U : Matrix (Fin n) (Fin n) k} (hU : uTriangular n U) :
    (M * U).submatrix rows (Fin.castLE hr) =
      M.submatrix rows (Fin.castLE hr) *
        U.submatrix (Fin.castLE hr) (Fin.castLE hr) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  let f := fun q : Fin n => M (rows i) q * U q (Fin.castLE hr j)
  calc
    ∑ q : Fin n, f q =
        ∑ q ∈ (Finset.univ.filter fun q : Fin n => q.val < r), f q := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hqr : r ≤ q.val := Nat.le_of_not_lt hq
      have hjqNat : (Fin.castLE hr j).val < q.val := lt_of_lt_of_le j.isLt hqr
      have hjq : Fin.castLE hr j < q := hjqNat
      simp [f, hU hjq]
    _ = ∑ q : {q : Fin n // q.val < r}, f q := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun q : Fin n => q.val < r))
        (by simp) f]
    _ = ∑ q : Fin r, f (Fin.castLE hr q) := by
      symm
      exact Fintype.sum_equiv (Fin.castLEquiv hr) _ _ (fun q => rfl)

private lemma submatrix_mul_of_lTriangular_left
    {n r m : ℕ} (hr : r ≤ n) (cols : Fin m → Fin n)
    {L M : Matrix (Fin n) (Fin n) k} (hL : lTriangular n L) :
    (L * M).submatrix (Fin.castLE hr) cols =
      L.submatrix (Fin.castLE hr) (Fin.castLE hr) *
        M.submatrix (Fin.castLE hr) cols := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  let f := fun q : Fin n => L (Fin.castLE hr i) q * M q (cols j)
  calc
    ∑ q : Fin n, f q =
        ∑ q ∈ (Finset.univ.filter fun q : Fin n => q.val < r), f q := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hqr : r ≤ q.val := Nat.le_of_not_lt hq
      have hiqNat : (Fin.castLE hr i).val < q.val := lt_of_lt_of_le i.isLt hqr
      have hiq : Fin.castLE hr i < q := hiqNat
      have hz : L (Fin.castLE hr i) q = 0 := by
        change tTriangular n (Matrix.transpose L) at hL
        exact hL hiq
      simp [f, hz]
    _ = ∑ q : {q : Fin n // q.val < r}, f q := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun q : Fin n => q.val < r))
        (by simp) f]
    _ = ∑ q : Fin r, f (Fin.castLE hr q) := by
      symm
      exact Fintype.sum_equiv (Fin.castLEquiv hr) _ _ (fun q => rfl)

private lemma leadingPrincipalSubmatrix_mul_of_lTriangular_left
    {n r : ℕ} (hr : r ≤ n) {L M : Matrix (Fin n) (Fin n) k}
    (hL : lTriangular n L) :
    leadingPrincipalSubmatrix (L * M) r hr =
      leadingPrincipalSubmatrix L r hr * leadingPrincipalSubmatrix M r hr := by
  ext i j
  simp only [leadingPrincipalSubmatrix, Matrix.submatrix_apply, Matrix.mul_apply]
  let f := fun q : Fin n => L (Fin.castLE hr i) q * M q (Fin.castLE hr j)
  calc
    ∑ q : Fin n, f q =
        ∑ q ∈ (Finset.univ.filter fun q : Fin n => q.val < r), f q := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hiqNat : (Fin.castLE hr i).val < q.val :=
        lt_of_lt_of_le i.isLt (Nat.le_of_not_lt hq)
      have hiq : Fin.castLE hr i < q := hiqNat
      have hz : L (Fin.castLE hr i) q = 0 := by
        change tTriangular n (Matrix.transpose L) at hL
        exact hL hiq
      simp [f, hz]
    _ = ∑ q : {q : Fin n // q.val < r}, f q := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun q : Fin n => q.val < r))
        (by simp) f]
    _ = ∑ q : Fin r, f (Fin.castLE hr q) := by
      symm
      exact Fintype.sum_equiv (Fin.castLEquiv hr) _ _ (fun q => rfl)

private lemma leadingPrincipalSubmatrix_mul_of_uTriangular_right
    {n r : ℕ} (hr : r ≤ n) {M U : Matrix (Fin n) (Fin n) k}
    (hU : uTriangular n U) :
    leadingPrincipalSubmatrix (M * U) r hr =
      leadingPrincipalSubmatrix M r hr * leadingPrincipalSubmatrix U r hr := by
  ext i j
  simp only [leadingPrincipalSubmatrix, Matrix.submatrix_apply, Matrix.mul_apply]
  let f := fun q : Fin n => M (Fin.castLE hr i) q * U q (Fin.castLE hr j)
  calc
    ∑ q : Fin n, f q =
        ∑ q ∈ (Finset.univ.filter fun q : Fin n => q.val < r), f q := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hjqNat : (Fin.castLE hr j).val < q.val :=
        lt_of_lt_of_le j.isLt (Nat.le_of_not_lt hq)
      have hjq : Fin.castLE hr j < q := hjqNat
      simp [f, hU hjq]
    _ = ∑ q : {q : Fin n // q.val < r}, f q := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun q : Fin n => q.val < r))
        (by simp) f]
    _ = ∑ q : Fin r, f (Fin.castLE hr q) := by
      symm
      exact Fintype.sum_equiv (Fin.castLEquiv hr) _ _ (fun q => rfl)

private lemma leadingPrincipalSubmatrix_diagonal
    {n r : ℕ} (hr : r ≤ n) (d : Fin n → k) :
    leadingPrincipalSubmatrix (Matrix.diagonal d) r hr =
      Matrix.diagonal (fun i => d (Fin.castLE hr i)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [leadingPrincipalSubmatrix]
  · have hcast : Fin.castLE hr i ≠ Fin.castLE hr j := fun h =>
      hij (Fin.castLE_injective hr h)
    simp [leadingPrincipalSubmatrix, hij, hcast]

private lemma leadingPrincipalSubmatrix_lUnipotent
    {n r : ℕ} (hr : r ≤ n) {L : Matrix (Fin n) (Fin n) k}
    (hL : lUnipotent n L) :
    lUnipotent r (leadingPrincipalSubmatrix L r hr) := by
  constructor
  · change tTriangular r (Matrix.transpose (leadingPrincipalSubmatrix L r hr))
    intro i j hij
    exact hL.1 (Fin.castLE_lt_castLE_iff hr |>.mpr hij)
  · intro i
    exact hL.2 (Fin.castLE hr i)

private lemma leadingPrincipalSubmatrix_uUnipotent
    {n r : ℕ} (hr : r ≤ n) {U : Matrix (Fin n) (Fin n) k}
    (hU : uUnipotent n U) :
    uUnipotent r (leadingPrincipalSubmatrix U r hr) := by
  constructor
  · intro i j hij
    exact hU.1 (Fin.castLE_lt_castLE_iff hr |>.mpr hij)
  · intro i
    exact hU.2 (Fin.castLE hr i)

public theorem LDUFactorization.leadingPrincipalMinor_eq_prod {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A)
    (r : ℕ) (hr : r ≤ n) :
    leadingPrincipalMinor A r hr =
      ∏ i : Fin r, F.diagonal (Fin.castLE hr i) := by
  rw [leadingPrincipalMinor]
  rw (occs := .pos [1]) [F.eq_matrix]
  rw [leadingPrincipalSubmatrix_mul_of_uTriangular_right hr F.upper_unitriangular.1]
  rw [leadingPrincipalSubmatrix_mul_of_lTriangular_left hr F.lower_unitriangular.1]
  rw [leadingPrincipalSubmatrix_diagonal]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hL := leadingPrincipalSubmatrix_lUnipotent hr F.lower_unitriangular
  have hU := leadingPrincipalSubmatrix_uUnipotent hr F.upper_unitriangular
  rw [lTriangular_det r hL.1, det_eq_one_of_uUnipotent r hU]
  simp [hL.2]

public theorem LDUFactorization.hasNonzeroLeadingPrincipalMinors {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) :
    HasNonzeroLeadingPrincipalMinors A := by
  intro r hr _
  rw [F.leadingPrincipalMinor_eq_prod r hr]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => F.diagonal_ne_zero _

private theorem exists_ldu_of_hasNonzeroLeadingPrincipalMinors :
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) k),
      HasNonzeroLeadingPrincipalMinors A → Nonempty (LDUFactorization A) := by
  intro n
  induction n with
  | zero =>
      intro A _
      exact ⟨{
        lower := 1
        diagonal := fun i => Fin.elim0 i
        upper := 1
        lower_unitriangular := ⟨by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
        diagonal_ne_zero := by intro i; exact Fin.elim0 i
        upper_unitriangular := ⟨by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
        eq_matrix := by ext i; exact Fin.elim0 i }⟩
  | succ n ih =>
      intro A hA
      let B : Matrix (Fin n) (Fin n) k := A.submatrix Fin.castSucc Fin.castSucc
      have hB : HasNonzeroLeadingPrincipalMinors B := by
        intro r hr hrpos
        have h := hA r (hr.trans (Nat.le_succ n)) hrpos
        have hsub : leadingPrincipalSubmatrix B r hr =
            leadingPrincipalSubmatrix A r (hr.trans (Nat.le_succ n)) := by
          ext i j
          rfl
        rw [leadingPrincipalMinor, hsub]
        exact h
      rcases ih B hB with ⟨FB⟩
      have hdetB : B.det ≠ 0 := by
        by_cases hn : n = 0
        · subst n
          simp [B]
        · simpa [leadingPrincipalMinor, leadingPrincipalSubmatrix, B] using
            hB n (le_refl n) (Nat.pos_of_ne_zero hn)
      let _ : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hdetB)
      let b : Matrix (Fin n) (Fin 1) k := A.submatrix Fin.castSucc (Fin.natAdd n)
      let c : Matrix (Fin 1) (Fin n) k := A.submatrix (Fin.natAdd n) Fin.castSucc
      let a : Matrix (Fin 1) (Fin 1) k := A.submatrix (Fin.natAdd n) (Fin.natAdd n)
      let s : Matrix (Fin 1) (Fin 1) k := a - c * ⅟B * b
      let q : k := s 0 0
      have hblock :
          Matrix.reindex (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm
              (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm A =
            Matrix.fromBlocks B b c a := by
        ext i j
        rcases i with i | i <;> rcases j with j | j <;> rfl
      have hq : q ≠ 0 := by
        have hfull := hA (n + 1) (le_refl _) (Nat.succ_pos n)
        rw [leadingPrincipalMinor, leadingPrincipalSubmatrix] at hfull
        have hdetA : A.det ≠ 0 := by simpa using hfull
        have hdetblock : (Matrix.fromBlocks B b c a).det ≠ 0 := by
          rw [← hblock, Matrix.det_reindex_self]
          exact hdetA
        rw [Matrix.det_fromBlocks₁₁] at hdetblock
        intro hq0
        apply hdetblock
        have hsdet : s.det = q := by
          simp [q, Matrix.det_unique]
        rw [show (a - c * ⅟B * b).det = 0 by
          change s.det = 0
          rw [hsdet, hq0]]
        simp
      let dsum : Fin n ⊕ Fin 1 → k := fun i =>
        match i with
        | Sum.inl j => FB.diagonal j
        | Sum.inr _ => q
      let Lsum : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) k :=
        Matrix.fromBlocks FB.lower 0 (c * ⅟B * FB.lower) 1
      let Usum : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) k :=
        Matrix.fromBlocks FB.upper (FB.upper * (⅟B * b)) 0 1
      let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
      let L := Matrix.reindex e e Lsum
      let U := Matrix.reindex e e Usum
      let d : Fin (n + 1) → k := fun i => dsum (e.symm i)
      refine ⟨{
        lower := L
        diagonal := d
        upper := U
        lower_unitriangular := ?_
        diagonal_ne_zero := ?_
        upper_unitriangular := ?_
        eq_matrix := ?_ }⟩
      · constructor
        · change tTriangular (n + 1) (Matrix.transpose L)
          intro i j hij
          change L j i = 0
          simp only [L, Matrix.reindex_apply, Matrix.submatrix_apply]
          generalize hi : e.symm i = ii at ⊢
          generalize hj : e.symm j = jj at ⊢
          rcases ii with ii | ii <;> rcases jj with jj | jj
          · apply FB.lower_unitriangular.1
            have hi' : i = e (Sum.inl ii) := by rw [← hi, Equiv.apply_symm_apply]
            have hj' : j = e (Sum.inl jj) := by rw [← hj, Equiv.apply_symm_apply]
            rw [hi', hj'] at hij
            change jj.val < ii.val at hij ⊢
            exact hij
          · have hi' : i = e (Sum.inl ii) := by rw [← hi, Equiv.apply_symm_apply]
            have hj' : j = e (Sum.inr jj) := by rw [← hj, Equiv.apply_symm_apply]
            rw [hi', hj'] at hij
            change n + jj.val < ii.val at hij
            omega
          · simp [Lsum]
          · have hs : (Sum.inr ii : Fin n ⊕ Fin 1) = Sum.inr jj := by
              congr 1
              exact Subsingleton.elim _ _
            have hijEq : i = j := e.symm.injective (hi.trans (hs.trans hj.symm))
            exact (lt_irrefl i (hijEq ▸ hij)).elim
        · intro i
          simp only [L, Matrix.reindex_apply, Matrix.submatrix_apply]
          generalize hi : e.symm i = ii at ⊢
          rcases ii with ii | ii
          · exact FB.lower_unitriangular.2 ii
          · fin_cases ii
            simp [Lsum]
      · intro i
        simp only [d]
        generalize hi : e.symm i = ii
        rcases ii with ii | ii
        · exact FB.diagonal_ne_zero ii
        · exact hq
      · constructor
        · intro i j hij
          simp only [U, Matrix.reindex_apply, Matrix.submatrix_apply]
          generalize hi : e.symm i = ii at ⊢
          generalize hj : e.symm j = jj at ⊢
          rcases ii with ii | ii <;> rcases jj with jj | jj
          · apply FB.upper_unitriangular.1
            have hi' : i = e (Sum.inl ii) := by rw [← hi, Equiv.apply_symm_apply]
            have hj' : j = e (Sum.inl jj) := by rw [← hj, Equiv.apply_symm_apply]
            rw [hi', hj'] at hij
            change jj.val < ii.val at hij ⊢
            exact hij
          · have hi' : i = e (Sum.inl ii) := by rw [← hi, Equiv.apply_symm_apply]
            have hj' : j = e (Sum.inr jj) := by rw [← hj, Equiv.apply_symm_apply]
            rw [hi', hj'] at hij
            change n + jj.val < ii.val at hij
            omega
          · simp [Usum]
          · have hs : (Sum.inr ii : Fin n ⊕ Fin 1) = Sum.inr jj := by
              congr 1
              exact Subsingleton.elim _ _
            have hijEq : i = j := e.symm.injective (hi.trans (hs.trans hj.symm))
            exact (lt_irrefl i (hijEq ▸ hij)).elim
        · intro i
          simp only [U, Matrix.reindex_apply, Matrix.submatrix_apply]
          generalize hi : e.symm i = ii at ⊢
          rcases ii with ii | ii
          · exact FB.upper_unitriangular.2 ii
          · fin_cases ii
            simp [Usum]
      · let R : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) k ≃+*
            Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
          Matrix.reindexRingEquiv k e
        have hdiag : R (Matrix.diagonal dsum) = Matrix.diagonal d := by
          ext i j
          simp [R, d, Matrix.diagonal_apply]
        have hfac : Matrix.fromBlocks B b c a =
            Lsum * Matrix.diagonal dsum * Usum := by
          have hdiagblock : Matrix.diagonal dsum =
              Matrix.fromBlocks (Matrix.diagonal FB.diagonal) 0 0
                (Matrix.diagonal fun _ : Fin 1 => q) := by
            symm
            simp [dsum]
          have hs : s = Matrix.diagonal fun _ : Fin 1 => q := by
            ext i j
            fin_cases i
            fin_cases j
            simp [s, q]
          rw [Matrix.fromBlocks_eq_of_invertible₁₁]
          rw [hdiagblock]
          simp only [Lsum, Usum, Matrix.fromBlocks_multiply, Matrix.mul_zero,
            Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
          simp_rw [← FB.eq_matrix]
          have hschur : a - c * ⅟B * b = Matrix.diagonal fun _ : Fin 1 => q := by
            simpa [s] using hs
          rw [hschur]
          have hFBr : FB.lower * (Matrix.diagonal FB.diagonal * FB.upper) = B := by
            rw [← Matrix.mul_assoc, ← FB.eq_matrix]
          have htop :
              FB.lower * (Matrix.diagonal FB.diagonal *
                (FB.upper * (⅟B * b))) = b := by
            calc
              _ = (FB.lower * (Matrix.diagonal FB.diagonal * FB.upper)) *
                    (⅟B * b) := by simp only [Matrix.mul_assoc]
              _ = B * (⅟B * b) := by rw [hFBr]
              _ = b := Matrix.mul_invOf_cancel_left B b
          rw [Matrix.fromBlocks_inj]
          refine ⟨rfl, ?_, ?_, ?_⟩
          · calc
              B * (⅟B * b) = b := Matrix.mul_invOf_cancel_left B b
              _ = FB.lower * (Matrix.diagonal FB.diagonal *
                    (FB.upper * (⅟B * b))) := htop.symm
              _ = FB.lower * Matrix.diagonal FB.diagonal *
                    (FB.upper * (⅟B * b)) := by rw [Matrix.mul_assoc]
          · simp [Matrix.mul_assoc, hFBr]
          · simp only [Matrix.mul_assoc]
            rw [htop]
            simp
        change R.symm A = Matrix.fromBlocks B b c a at hblock
        calc
          A = R (R.symm A) := (R.apply_symm_apply A).symm
          _ = R (Matrix.fromBlocks B b c a) := congrArg R hblock
          _ = R (Lsum * Matrix.diagonal dsum * Usum) := congrArg R hfac
          _ = R Lsum * R (Matrix.diagonal dsum) * R Usum := by
            rw [map_mul, map_mul]
          _ = L * Matrix.diagonal d * U := by
            change R Lsum * R (Matrix.diagonal dsum) * R Usum =
              R Lsum * Matrix.diagonal d * R Usum
            exact congrArg (fun M => R Lsum * M * R Usum) hdiag

public theorem exists_ldu_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    Nonempty (LDUFactorization A) ↔ HasNonzeroLeadingPrincipalMinors A := by
  constructor
  · rintro ⟨F⟩
    exact F.hasNonzeroLeadingPrincipalMinors
  · exact exists_ldu_of_hasNonzeroLeadingPrincipalMinors A

private lemma lUnipotent_eq_one_of_uTriangular {n : ℕ}
    {M : Matrix (Fin n) (Fin n) k} (hL : lUnipotent n M)
    (hU : uTriangular n M) : M = 1 := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · have hz : Matrix.transpose M j i = 0 := hL.1 (i := j) (j := i) hij
    change M i j = 0 at hz
    rw [hz]
    simp [ne_of_lt hij]
  · subst j
    simp [hL.2]
  · rw [hU hij]
    simp [ne_of_gt hij]

public theorem LDUFactorization.unique {n : ℕ} {A : Matrix (Fin n) (Fin n) k}
    (F G : LDUFactorization A) :
    F.lower = G.lower ∧ F.diagonal = G.diagonal ∧ F.upper = G.upper := by
  let DF := Matrix.diagonal F.diagonal
  let DG := Matrix.diagonal G.diagonal
  let _ : Invertible F.lower := Matrix.invertibleOfIsUnitDet F.lower <| by
    rw [lTriangular_det n F.lower_unitriangular.1]
    simp [F.lower_unitriangular.2]
  let _ : Invertible G.lower := Matrix.invertibleOfIsUnitDet G.lower <| by
    rw [lTriangular_det n G.lower_unitriangular.1]
    simp [G.lower_unitriangular.2]
  let _ : Invertible F.upper := Matrix.invertibleOfIsUnitDet F.upper <| by
    rw [det_eq_one_of_uUnipotent n F.upper_unitriangular]
    exact isUnit_one
  let _ : Invertible G.upper := Matrix.invertibleOfIsUnitDet G.upper <| by
    rw [det_eq_one_of_uUnipotent n G.upper_unitriangular]
    exact isUnit_one
  let _ : Invertible DF := Matrix.invertibleOfIsUnitDet DF <| by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun i _ =>
      F.diagonal_ne_zero i
  let _ : Invertible DG := Matrix.invertibleOfIsUnitDet DG <| by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun i _ =>
      G.diagonal_ne_zero i
  have heq : F.lower * DF * F.upper = G.lower * DG * G.upper := by
    rw [← F.eq_matrix, ← G.eq_matrix]
  have hquot : ⅟G.lower * F.lower = DG * G.upper * ⅟F.upper * ⅟DF := by
    calc
      ⅟G.lower * F.lower =
          ⅟G.lower * (F.lower * DF * F.upper) * ⅟F.upper * ⅟DF := by
        simp [Matrix.mul_assoc]
      _ = ⅟G.lower * (G.lower * DG * G.upper) * ⅟F.upper * ⅟DF := by rw [heq]
      _ = DG * G.upper * ⅟F.upper * ⅟DF := by simp [Matrix.mul_assoc]
  have hquotL : lUnipotent n (⅟G.lower * F.lower) := by
    apply lUnipotent_mul n
    · rw [Matrix.invOf_eq_nonsing_inv]
      exact lUnipotent_inv n G.lower_unitriangular
    · exact F.lower_unitriangular
  have hDF : uTriangular n DF := by
    intro i j hij
    simp [DF, ne_of_gt hij]
  have hDG : uTriangular n DG := by
    intro i j hij
    simp [DG, ne_of_gt hij]
  have hquotU : uTriangular n (⅟G.lower * F.lower) := by
    rw [hquot]
    apply uTriangular_mul n (uTriangular_mul n (uTriangular_mul n hDG
      G.upper_unitriangular.1) ?_) ?_
    · rw [Matrix.invOf_eq_nonsing_inv]
      exact (uUnipotent_inv n F.upper_unitriangular).1
    · rw [Matrix.invOf_eq_nonsing_inv]
      exact tTriangular_inv n hDF (Matrix.isUnit_det_of_invertible DF)
  have hquotOne : ⅟G.lower * F.lower = 1 :=
    lUnipotent_eq_one_of_uTriangular hquotL hquotU
  have hlower : F.lower = G.lower := by
    have h := congrArg (fun M => G.lower * M) hquotOne
    simpa [Matrix.mul_assoc] using h
  have hDU : DF * F.upper = DG * G.upper := by
    apply Matrix.mul_right_injective_of_invertible F.lower
    simpa [hlower, Matrix.mul_assoc] using heq
  have hdiagonal : F.diagonal = G.diagonal := by
    funext i
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M i i) hDU
    have hFdiag : (DF * F.upper) i i = F.diagonal i := by
      rw [tTriangular_mul_apply_diag n hDF F.upper_unitriangular.1]
      simp [DF, F.upper_unitriangular.2]
    have hGdiag : (DG * G.upper) i i = G.diagonal i := by
      rw [tTriangular_mul_apply_diag n hDG G.upper_unitriangular.1]
      simp [DG, G.upper_unitriangular.2]
    simpa [hFdiag, hGdiag] using h
  have hupper : F.upper = G.upper := by
    apply Matrix.mul_right_injective_of_invertible DF
    simpa [DF, DG, hdiagonal] using hDU
  exact ⟨hlower, hdiagonal, hupper⟩

public theorem LDUFactorization.leadingPrincipalMinor_succ {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i : Fin n) :
    leadingPrincipalMinor A (i.val + 1) (Nat.succ_le_iff.mpr i.isLt) =
      leadingPrincipalMinor A i.val (Nat.le_of_lt i.isLt) * F.diagonal i := by
  rw [F.leadingPrincipalMinor_eq_prod (i.val + 1) (Nat.succ_le_iff.mpr i.isLt)]
  rw [F.leadingPrincipalMinor_eq_prod i.val (Nat.le_of_lt i.isLt)]
  rw [Fin.prod_univ_castSucc]
  congr 1

private lemma lowerBorderSubmatrix_lTriangular {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i j : Fin n) :
    lTriangular (j.val + 1)
      (F.lower.submatrix (lowerBorderRow i j)
        (Fin.castLE (Nat.succ_le_iff.mpr j.isLt))) := by
  change tTriangular (j.val + 1) (Matrix.transpose
    (F.lower.submatrix (lowerBorderRow i j)
      (Fin.castLE (Nat.succ_le_iff.mpr j.isLt))))
  intro a b hba
  change F.lower (lowerBorderRow i j b)
    (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) a) = 0
  apply F.lower_unitriangular.1
  have hb : b.val < j.val := by omega
  change (lowerBorderRow i j b).val < a.val
  simpa [lowerBorderRow, hb] using hba

private lemma lowerBorderSubmatrix_det {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i j : Fin n) :
    (F.lower.submatrix (lowerBorderRow i j)
      (Fin.castLE (Nat.succ_le_iff.mpr j.isLt))).det = F.lower i j := by
  rw [lTriangular_det (j.val + 1) (lowerBorderSubmatrix_lTriangular F i j)]
  rw [Fin.prod_univ_castSucc]
  simp only [Matrix.submatrix_apply]
  have hprod : (∏ r : Fin j.val,
      F.lower (lowerBorderRow i j r.castSucc)
        (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) r.castSucc)) = 1 := by
    apply Finset.prod_eq_one
    intro r _
    rw [show lowerBorderRow i j r.castSucc =
        Fin.castLE (Nat.succ_le_iff.mpr j.isLt) r.castSucc by
      apply Fin.ext
      simp [lowerBorderRow, r.isLt]]
    exact F.lower_unitriangular.2 _
  rw [hprod, one_mul]
  congr 1
  all_goals
    apply Fin.ext
    simp [lowerBorderRow]

/-- A lower-factor entry times its leading principal minor is the corresponding
row-bordered minor. -/
public theorem LDUFactorization.lowerBorderedMinor_eq {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i j : Fin n) :
    lowerBorderedMinor A i j = F.lower i j *
      leadingPrincipalMinor A (j.val + 1) (Nat.succ_le_iff.mpr j.isLt) := by
  have hD : uTriangular n (Matrix.diagonal F.diagonal) := by
    intro a b hba
    simp [ne_of_gt hba]
  have hU := leadingPrincipalSubmatrix_uUnipotent
    (Nat.succ_le_iff.mpr j.isLt) F.upper_unitriangular
  change uUnipotent (j.val + 1)
    (F.upper.submatrix (Fin.castLE (Nat.succ_le_iff.mpr j.isLt))
      (Fin.castLE (Nat.succ_le_iff.mpr j.isLt))) at hU
  rw [lowerBorderedMinor]
  rw (occs := .pos [1]) [F.eq_matrix]
  rw [submatrix_mul_of_uTriangular_right (Nat.succ_le_iff.mpr j.isLt)
    (lowerBorderRow i j) F.upper_unitriangular.1]
  rw [submatrix_mul_of_uTriangular_right (Nat.succ_le_iff.mpr j.isLt)
    (lowerBorderRow i j) hD]
  rw [Matrix.det_mul, Matrix.det_mul, lowerBorderSubmatrix_det F i j]
  rw [show (Matrix.diagonal F.diagonal).submatrix
      (Fin.castLE (Nat.succ_le_iff.mpr j.isLt))
      (Fin.castLE (Nat.succ_le_iff.mpr j.isLt)) =
        Matrix.diagonal (fun a => F.diagonal
          (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) a)) by
      exact leadingPrincipalSubmatrix_diagonal _ _]
  rw [Matrix.det_diagonal]
  rw [det_eq_one_of_uUnipotent (j.val + 1) hU, mul_one]
  rw [F.leadingPrincipalMinor_eq_prod (j.val + 1)
    (Nat.succ_le_iff.mpr j.isLt)]

private lemma upperBorderSubmatrix_uTriangular {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i j : Fin n) :
    uTriangular (i.val + 1)
      (F.upper.submatrix (Fin.castLE (Nat.succ_le_iff.mpr i.isLt))
        (upperBorderColumn i j)) := by
  intro a b hba
  change F.upper (Fin.castLE (Nat.succ_le_iff.mpr i.isLt) a)
    (upperBorderColumn i j b) = 0
  apply F.upper_unitriangular.1
  have hb : b.val < i.val := by omega
  change (upperBorderColumn i j b).val < a.val
  simpa [upperBorderColumn, hb] using hba

private lemma upperBorderSubmatrix_det {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i j : Fin n) :
    (F.upper.submatrix (Fin.castLE (Nat.succ_le_iff.mpr i.isLt))
      (upperBorderColumn i j)).det = F.upper i j := by
  rw [det_eq_prod_diagonal_of_tTriangular (i.val + 1)
    (upperBorderSubmatrix_uTriangular F i j)]
  rw [Fin.prod_univ_castSucc]
  simp only [Matrix.submatrix_apply]
  have hprod : (∏ r : Fin i.val,
      F.upper (Fin.castLE (Nat.succ_le_iff.mpr i.isLt) r.castSucc)
        (upperBorderColumn i j r.castSucc)) = 1 := by
    apply Finset.prod_eq_one
    intro r _
    rw [show upperBorderColumn i j r.castSucc =
        Fin.castLE (Nat.succ_le_iff.mpr i.isLt) r.castSucc by
      apply Fin.ext
      simp [upperBorderColumn, r.isLt]]
    exact F.upper_unitriangular.2 _
  rw [hprod, one_mul]
  congr 1
  all_goals
    apply Fin.ext
    simp [upperBorderColumn]

/-- An upper-factor entry times its leading principal minor is the corresponding
column-bordered minor. -/
public theorem LDUFactorization.upperBorderedMinor_eq {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i j : Fin n) :
    upperBorderedMinor A i j = F.upper i j *
      leadingPrincipalMinor A (i.val + 1) (Nat.succ_le_iff.mpr i.isLt) := by
  have hD : lTriangular n (Matrix.diagonal F.diagonal) := by
    change tTriangular n (Matrix.transpose (Matrix.diagonal F.diagonal))
    intro a b hba
    simp [ne_of_lt hba]
  have hL := leadingPrincipalSubmatrix_lUnipotent
    (Nat.succ_le_iff.mpr i.isLt) F.lower_unitriangular
  change lUnipotent (i.val + 1)
    (F.lower.submatrix (Fin.castLE (Nat.succ_le_iff.mpr i.isLt))
      (Fin.castLE (Nat.succ_le_iff.mpr i.isLt))) at hL
  rw [upperBorderedMinor]
  rw (occs := .pos [1]) [F.eq_matrix]
  rw [Matrix.mul_assoc]
  rw [submatrix_mul_of_lTriangular_left (Nat.succ_le_iff.mpr i.isLt)
    (upperBorderColumn i j) F.lower_unitriangular.1]
  rw [submatrix_mul_of_lTriangular_left (Nat.succ_le_iff.mpr i.isLt)
    (upperBorderColumn i j) hD]
  rw [Matrix.det_mul, Matrix.det_mul]
  rw [lTriangular_det (i.val + 1) hL.1]
  simp only [hL.2, Finset.prod_const_one, one_mul]
  rw [show (Matrix.diagonal F.diagonal).submatrix
      (Fin.castLE (Nat.succ_le_iff.mpr i.isLt))
      (Fin.castLE (Nat.succ_le_iff.mpr i.isLt)) =
        Matrix.diagonal (fun a => F.diagonal
          (Fin.castLE (Nat.succ_le_iff.mpr i.isLt) a)) by
      exact leadingPrincipalSubmatrix_diagonal _ _]
  rw [Matrix.det_diagonal, upperBorderSubmatrix_det F i j]
  rw [F.leadingPrincipalMinor_eq_prod (i.val + 1)
    (Nat.succ_le_iff.mpr i.isLt)]
  simp [mul_comm]

/-- Cramer's-rule form of the lower-factor entry formula. -/
public theorem LDUFactorization.lower_eq_borderedMinor_div {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i j : Fin n) :
    F.lower i j = lowerBorderedMinor A i j /
      leadingPrincipalMinor A (j.val + 1) (Nat.succ_le_iff.mpr j.isLt) := by
  apply (eq_div_iff (F.hasNonzeroLeadingPrincipalMinors (j.val + 1)
    (Nat.succ_le_iff.mpr j.isLt) (Nat.succ_pos j.val))).2
  exact F.lowerBorderedMinor_eq i j |>.symm

/-- Cramer's-rule form of the upper-factor entry formula. -/
public theorem LDUFactorization.upper_eq_borderedMinor_div {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i j : Fin n) :
    F.upper i j = upperBorderedMinor A i j /
      leadingPrincipalMinor A (i.val + 1) (Nat.succ_le_iff.mpr i.isLt) := by
  apply (eq_div_iff (F.hasNonzeroLeadingPrincipalMinors (i.val + 1)
    (Nat.succ_le_iff.mpr i.isLt) (Nat.succ_pos i.val))).2
  exact F.upperBorderedMinor_eq i j |>.symm

/-- Each diagonal pivot is the quotient of two consecutive leading principal
minors (with the empty leading minor serving as the denominator at `i = 0`). -/
public theorem LDUFactorization.diagonal_eq_leadingPrincipalMinor_div {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (F : LDUFactorization A) (i : Fin n) :
    F.diagonal i =
      leadingPrincipalMinor A (i.val + 1) (Nat.succ_le_iff.mpr i.isLt) /
        leadingPrincipalMinor A i.val (Nat.le_of_lt i.isLt) := by
  have hprev : leadingPrincipalMinor A i.val (Nat.le_of_lt i.isLt) ≠ 0 := by
    by_cases hi : i.val = 0
    · let _ : IsEmpty (Fin i.val) := ⟨fun j => by
        have : j.val < 0 := by simpa [hi] using j.isLt
        omega⟩
      simp [leadingPrincipalMinor]
    · exact F.hasNonzeroLeadingPrincipalMinors i.val (Nat.le_of_lt i.isLt)
        (Nat.pos_of_ne_zero hi)
  apply (eq_div_iff hprev).2
  rw [mul_comm]
  exact (F.leadingPrincipalMinor_succ i).symm

/-- Gaussian multiplication has precisely the matrices whose nonempty leading
principal minors are nonzero as its range. -/
public theorem range_lduFactors_multiply {n : ℕ} :
    Set.range (LDUFactors.multiply (k := k) (n := n)) =
      {A | HasNonzeroLeadingPrincipalMinors A} := by
  ext A
  constructor
  · rintro ⟨F, rfl⟩
    exact F.factorization.hasNonzeroLeadingPrincipalMinors
  · intro hA
    rcases exists_ldu_of_hasNonzeroLeadingPrincipalMinors A hA with ⟨F⟩
    refine ⟨{
      lower := F.lower
      diagonal := F.diagonal
      upper := F.upper
      lower_unitriangular := F.lower_unitriangular
      diagonal_ne_zero := F.diagonal_ne_zero
      upper_unitriangular := F.upper_unitriangular }, ?_⟩
    exact F.eq_matrix.symm

/-- Uniqueness of Gaussian LDU factors, expressed as injectivity of the
multiplication map. -/
public theorem lduFactors_multiply_injective {n : ℕ} :
    Function.Injective (LDUFactors.multiply (k := k) (n := n)) := by
  intro F G hFG
  let GG : LDUFactorization F.multiply := {
    lower := G.lower
    diagonal := G.diagonal
    upper := G.upper
    lower_unitriangular := G.lower_unitriangular
    diagonal_ne_zero := G.diagonal_ne_zero
    upper_unitriangular := G.upper_unitriangular
    eq_matrix := hFG }
  have h := F.factorization.unique GG
  apply LDUFactors.ext
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- A matrix has unique LDU factors exactly when all of its nonempty leading
principal minors are nonzero. -/
public theorem exists_unique_ldu_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    (∃! F : LDUFactors (k := k) n, F.multiply = A) ↔
      HasNonzeroLeadingPrincipalMinors A := by
  constructor
  · rintro ⟨F, hF, -⟩
    have hfactorization : LDUFactorization A := {
      lower := F.lower
      diagonal := F.diagonal
      upper := F.upper
      lower_unitriangular := F.lower_unitriangular
      diagonal_ne_zero := F.diagonal_ne_zero
      upper_unitriangular := F.upper_unitriangular
      eq_matrix := hF.symm }
    exact hfactorization.hasNonzeroLeadingPrincipalMinors
  · intro hA
    have hrange : A ∈ Set.range (LDUFactors.multiply (k := k) (n := n)) := by
      rw [range_lduFactors_multiply]
      exact hA
    rcases hrange with ⟨F, hF⟩
    refine ⟨F, hF, ?_⟩
    intro G hG
    apply lduFactors_multiply_injective
    exact hG.trans hF.symm

section GLPrincipalOpen

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The coordinate polynomial for a leading principal minor on `GLₙ`. -/
@[expose]
public noncomputable def glLeadingPrincipalMinorPolynomial (n r : ℕ)
    (hr : r ≤ n) :
    MvPolynomial (glVariety (k := k) n).Coordinates k :=
  MvPolynomial.rename
    (fun p : Fin r × Fin r =>
      Sum.inl (Fin.castLE hr p.1, Fin.castLE hr p.2))
    (Matrix.det (Matrix.mvPolynomialX (Fin r) (Fin r) k))

omit [IsAlgClosed k] in
public lemma eval_glLeadingPrincipalMinorPolynomial (n r : ℕ)
    (hr : r ≤ n) (x : Variety.Point (glVariety n : Variety k)) :
    evalPolynomial x.val (glLeadingPrincipalMinorPolynomial (k := k) n r hr) =
      leadingPrincipalMinor (glMatrixOfPoint n x) r hr := by
  rw [glLeadingPrincipalMinorPolynomial, evalPolynomial_rename]
  change MvPolynomial.eval
    (fun p : Fin r × Fin r => x.val (Sum.inl (Fin.castLE hr p.1, Fin.castLE hr p.2)))
      (Matrix.det (Matrix.mvPolynomialX (Fin r) (Fin r) k)) = _
  rw [Matrix.eval_det_mvPolynomialX]
  rfl

/-- The finite family of all nonempty leading principal-minor polynomials. -/
@[expose]
public noncomputable def glLduLeadingMinorFamily (n : ℕ) :
    Fin n → MvPolynomial (glVariety (k := k) n).Coordinates k :=
  fun i => glLeadingPrincipalMinorPolynomial (k := k) n (i.val + 1)
    (Nat.succ_le_iff.mpr i.isLt)

/-- The matrix LDU big cell inside the presented `GLₙ` variety. -/
@[expose]
public noncomputable def glLduPrincipalOpenLocus (n : ℕ) :
    Set (Variety.Point (glVariety (k := k) n : Variety k)) :=
  (glVariety (k := k) n : Variety k).principalOpenLocus
    (glLduLeadingMinorFamily (k := k) n)

omit [IsAlgClosed k] in
public theorem glLduPrincipalOpenLocus_isZariskiOpen (n : ℕ) :
    IsZariskiOpen (glVariety (k := k) n : Variety k) (glLduPrincipalOpenLocus (k := k) n) :=
  Variety.principalOpenLocus_isZariskiOpen _ _

omit [IsAlgClosed k] in
public theorem mem_glLduPrincipalOpenLocus_iff (n : ℕ)
    (x : Variety.Point (glVariety (k := k) n : Variety k)) :
    x ∈ glLduPrincipalOpenLocus (k := k) n ↔
      HasNonzeroLeadingPrincipalMinors (glMatrixOfPoint n x) := by
  rw [glLduPrincipalOpenLocus, Variety.mem_principalOpenLocus]
  constructor
  · intro hx r hr hrpos
    let i : Fin n := ⟨r - 1, by omega⟩
    have hir : i.val + 1 = r := by simp [i]; omega
    have h := hx i
    rw [glLduLeadingMinorFamily, eval_glLeadingPrincipalMinorPolynomial] at h
    simpa [hir] using h
  · intro h i
    rw [glLduLeadingMinorFamily, eval_glLeadingPrincipalMinorPolynomial]
    exact h (i.val + 1) (Nat.succ_le_iff.mpr i.isLt) (Nat.succ_pos i.val)

omit [IsAlgClosed k] in
public theorem mem_glLduPrincipalOpenLocus_iff_lduRange (n : ℕ)
    (x : Variety.Point (glVariety (k := k) n : Variety k)) :
    x ∈ glLduPrincipalOpenLocus (k := k) n ↔
      glMatrixOfPoint n x ∈ Set.range (LDUFactors.multiply (k := k) (n := n)) := by
  rw [mem_glLduPrincipalOpenLocus_iff, range_lduFactors_multiply]
  rfl

end GLPrincipalOpen

end Theory.AlgebraicGroup
