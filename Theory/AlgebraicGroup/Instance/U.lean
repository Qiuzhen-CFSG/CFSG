module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.NoncommRing
public import Theory.AlgebraicGroup.Instance.Triangular
public import Theory.AlgebraicGroup.Jordan.FiniteOrder
public import Theory.AlgebraicGroup.Unipotent.Defs
public import Theory.AlgebraicGroup.Variety.AffineSpace

universe u

namespace Theory.AlgebraicGroup

section

open scoped TensorProduct
open LinearMap Submodule

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def uTriangular (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ ⦃i j : Fin n⦄, j < i → A i j = 0

/-- Upper-unitriangular matrices, with all diagonal entries equal to one. -/
@[expose]
public def uUnipotent (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : Prop :=
  uTriangular n A ∧ ∀ i : Fin n, A i i = 1

omit [IsAlgClosed k] in
/-- Upper-triangular matrices are closed under multiplication. -/
public lemma uTriangular_mul (n : ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : uTriangular n A) (hB : uTriangular n B) : uTriangular n (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hli : l < i
  · rw [hA hli, zero_mul]
  · have hjl : j < l := lt_of_lt_of_le hij (le_of_not_gt hli)
    rw [hB hjl, mul_zero]

omit [IsAlgClosed k] in
/-- Upper-unitriangular matrices are closed under multiplication. -/
public lemma uUnipotent_mul (n : ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : uUnipotent n A) (hB : uUnipotent n B) : uUnipotent n (A * B) := by
  constructor
  · exact uTriangular_mul n hA.1 hB.1
  · intro i
    rw [Matrix.mul_apply]
    have hsum : (∑ l : Fin n, A i l * B l i) = A i i * B i i := by
      apply Finset.sum_eq_single i
      · intro l hl hli
        by_cases hli' : l < i
        · rw [hA.1 hli', zero_mul]
        · have hil : i < l := lt_of_le_of_ne (le_of_not_gt hli') (Ne.symm hli)
          rw [hB.1 hil, mul_zero]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    rw [hsum, hA.2 i, hB.2 i]
    simp

/-- A permutation satisfying `σ i ≤ i` for every `i` is the identity. -/
public lemma perm_eq_id_of_le (n : ℕ) (σ : Equiv.Perm (Fin n))
    (h : ∀ i : Fin n, σ i ≤ i) : σ = 1 := by
  apply Equiv.ext
  intro i
  by_contra hne
  have hlt : σ i < i := lt_of_le_of_ne (h i) hne
  have hsum_eq : (∑ j : Fin n, (σ j : ℕ)) = (∑ j : Fin n, (j : ℕ)) := by
    simpa using (Equiv.sum_comp σ (fun j : Fin n => (j : ℕ)))
  have hle_sum : (∑ j : Fin n, (σ j : ℕ)) < (∑ j : Fin n, (j : ℕ)) := by
    exact Finset.sum_lt_sum (fun j hj => (h j : (σ j : ℕ) ≤ (j : ℕ)))
      ⟨i, Finset.mem_univ i, (hlt : (σ i : ℕ) < (i : ℕ))⟩
  exact (not_lt_of_ge hsum_eq.ge) hle_sum

omit [IsAlgClosed k] in
/-- The determinant of an upper-triangular matrix is the product of its diagonal entries. -/
public lemma det_eq_prod_diagonal_of_uTriangular (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : uTriangular n A) : A.det = ∏ i : Fin n, A i i := by
  rw [Matrix.det_apply]
  have hmem : ∀ σ : Equiv.Perm (Fin n), σ ≠ 1 → (Equiv.Perm.sign σ) • (∏ i, A (σ i) i) = 0 := by
    intro σ hσ
    have hle : ∃ i : Fin n, i < σ i := by
      by_contra h'
      apply hσ
      exact perm_eq_id_of_le n σ (by
        intro i
        exact le_of_not_gt (by intro h; exact h' ⟨i, h⟩))
    rcases hle with ⟨i₀, hi₀⟩
    have hz : A (σ i₀) i₀ = 0 := hA (i := σ i₀) (j := i₀) (by exact hi₀)
    have hprod : (∏ j : Fin n, A (σ j) j) = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (by simpa using hz)]
    simp [hprod]
  have hmain : (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ) • (∏ i, A (σ i) i)) =
      (Equiv.Perm.sign (1 : Equiv.Perm (Fin n))) • (∏ i, A i i) := by
    apply Finset.sum_eq_single (1 : Equiv.Perm (Fin n))
    · intro b hb hb1
      exact hmem b hb1
    · intro h1
      exact False.elim (h1 (Finset.mem_univ _))
  rw [hmain]
  simp

omit [IsAlgClosed k] in
/-- The determinant of an upper-unitriangular matrix is one. -/
public lemma det_eq_one_of_uUnipotent (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : uUnipotent n A) : A.det = 1 := by
  rw [det_eq_prod_diagonal_of_uTriangular n hA.1]
  exact Finset.prod_eq_one (fun i hi => hA.2 i)

omit [IsAlgClosed k] in
/-- The adjugate of an upper-triangular matrix is upper triangular. -/
public lemma adjugate_upperTriangular (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : uTriangular n A) ⦃i j : Fin n⦄ (hij : j < i) : (Matrix.adjugate A) i j = 0 := by
  rw [Matrix.adjugate_apply]
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  by_cases hσid : σ = 1
  · have hne : i ≠ j := ne_of_gt hij
    have hprod : (∏ l : Fin n, (A.updateRow j (Pi.single i 1)) (σ l) l) = 0 := by
      rw [hσid]
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by
        simp [Matrix.updateRow_apply, Pi.single, Ne.symm hne])]
    simp [hprod]
  · have hup : ∃ l : Fin n, l < σ l := by
      by_contra h'
      apply hσid
      exact perm_eq_id_of_le n σ (by
        intro l
        exact le_of_not_gt (by intro h; exact h' ⟨l, h⟩))
    rcases hup with ⟨l, hl⟩
    by_cases hσl : σ l = j
    · have hli : l ≠ i := by
        intro hli
        subst hli
        exact (not_lt_of_ge (le_of_lt hij)) (by simpa [hσl] using hl)
      have hprod : (∏ t : Fin n, (A.updateRow j (Pi.single i 1)) (σ t) t) = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ l) (by
          simp [hσl, Matrix.updateRow_apply, Pi.single, hli])]
      simp [hprod]
    · have hz : A (σ l) l = 0 := hA (i := σ l) (j := l) hl
      have hprod : (∏ t : Fin n, (A.updateRow j (Pi.single i 1)) (σ t) t) = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ l) (by
          simp [Matrix.updateRow_apply, hσl, hz])]
      simp [hprod]

omit [IsAlgClosed k] in
/-- The adjugate of an upper-unitriangular matrix is upper-unitriangular. -/
public lemma uUnipotent_adjugate (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : uUnipotent n A) : uUnipotent n (Matrix.adjugate A) := by
  constructor
  · intro i j hij
    exact adjugate_upperTriangular n hA.1 hij
  · intro i
    -- On the diagonal, the product with the adjugate reduces to the single
    -- term `k = i` because of upper triangularity.
    have hmul := congrArg (fun M : Matrix (Fin n) (Fin n) k => M i i) (Matrix.mul_adjugate A)
    have hdet1 : A.det = 1 := det_eq_one_of_uUnipotent n hA
    have hleft : (A * Matrix.adjugate A) i i = 1 := by
      rw [hmul, hdet1]
      simp
    have hsum : (∑ k : Fin n, A i k * (Matrix.adjugate A) k i) =
        A i i * (Matrix.adjugate A) i i := by
      apply Finset.sum_eq_single i
      · intro k hk hki
        by_cases hki' : k < i
        · rw [hA.1 hki', zero_mul]
        · have hik : i < k := lt_of_le_of_ne (le_of_not_gt hki') (Ne.symm hki)
          have hz : (Matrix.adjugate A) k i = 0 := adjugate_upperTriangular n hA.1 hik
          rw [hz, mul_zero]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    have hmain : A i i * (Matrix.adjugate A) i i = 1 := by
      rw [← hsum]
      simpa [Matrix.mul_apply] using hleft
    -- A i i = 1——(adjugate A) i i = 1
    have hAii : A i i = 1 := hA.2 i
    have : (1 : k) * (Matrix.adjugate A) i i = 1 := by
      simpa [hAii] using hmain
    simpa using this

omit [IsAlgClosed k] in
/-- The inverse of an upper-unitriangular matrix is its adjugate. -/
public lemma uUnipotent_inv_eq_adjugate (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : uUnipotent n A) : A⁻¹ = Matrix.adjugate A := by
  have hdet1 : A.det = 1 := det_eq_one_of_uUnipotent n hA
  have hIsUnit : IsUnit A.det := by
    rw [hdet1]
    exact isUnit_one
  rw [Matrix.nonsing_inv_apply (A := A) hIsUnit]
  rw [show (↑hIsUnit.unit⁻¹ : k) = 1 by
    simp [hdet1]]
  simp

omit [IsAlgClosed k] in
/-- The inverse of an upper-unitriangular matrix is upper-unitriangular. -/
public lemma uUnipotent_inv (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : uUnipotent n A) : uUnipotent n A⁻¹ := by
  rw [uUnipotent_inv_eq_adjugate n hA]
  exact uUnipotent_adjugate n hA

/-- The upper-unitriangular matrices form a subgroup of `GLₙ`. -/
@[expose]
public def uUnipotentGL (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) : Subgroup (GL (Fin n) k) where
  carrier := {g : GL (Fin n) k | uUnipotent n g.1}
  one_mem' := by
    constructor
    · intro i j hij
      simp [ne_of_gt hij]
    · intro i
      simp
  mul_mem' := by
    intro a b ha hb
    exact uUnipotent_mul n ha hb
  inv_mem' := by
    intro a ha
    -- The underlying matrix of `a⁻¹` is the inverse matrix of `a`.
    have hdet1 : a.1.det = 1 := det_eq_one_of_uUnipotent n ha
    have hinv : (a⁻¹ : GL (Fin n) k).1 = a.1⁻¹ := by
      exact (Units.inv_eq_of_mul_eq_one_right (u := a) (a := a.1⁻¹) (by
        exact Matrix.mul_nonsing_inv a.1 (a.isUnit.map Matrix.detMonoidHom)))
    change uUnipotent n ((a⁻¹ : GL (Fin n) k).1)
    rw [hinv]
    exact uUnipotent_inv n ha

/-- Affine equations for `Uₙ`: upper triangularity and diagonal entries equal to one. -/
public abbrev uVariety (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) : Variety k where
  Coordinates := ULift.{u} (Fin n × Fin n)
  finiteCoordinates := inferInstance
  equations : Set (MvPolynomial (ULift.{u} (Fin n × Fin n)) k) :=
    {p | (∃ i j : Fin n, j < i ∧ p = MvPolynomial.X (ULift.up (i, j))) ∨
         (∃ i : Fin n, p = MvPolynomial.X (ULift.up (i, i)) - 1)}

/-- Matrix component of a `Uₙ` point. -/
@[expose]
public def uPointMatrix (n : ℕ) (x : Variety.Point (uVariety k n)) :
    Matrix (Fin n) (Fin n) k :=
  fun i j => x.val (ULift.up (i, j))

/-- A `Uₙ` point satisfies the upper-unitriangular conditions. -/
public lemma uPoint_uUnipotent (n : ℕ) (x : Variety.Point (uVariety k n)) :
    uUnipotent n (uPointMatrix n x) := by
  constructor
  · intro i j hij
    have h := x.isZero (MvPolynomial.X (ULift.up (i, j))) (by
      exact Set.mem_ofPred.mpr (Or.inl ⟨i, j, hij, rfl⟩))
    simpa [uPointMatrix, evalPolynomial] using h
  · intro i
    have h := x.isZero (MvPolynomial.X (ULift.up (i, i)) - 1) (by
      exact Set.mem_ofPred.mpr (Or.inr ⟨i, rfl⟩))
    have hsum : evalPolynomial x.val (MvPolynomial.X (ULift.up (i, i))) - 1 = 0 := by
      simpa [evalPolynomial] using h
    have h' : evalPolynomial x.val (MvPolynomial.X (ULift.up (i, i))) = 1 := sub_eq_zero.mp hsum
    simpa [uPointMatrix, evalPolynomial] using h'

/-- The determinant of a `Uₙ` point is a unit. -/
public lemma uPoint_det_isUnit (n : ℕ) (x : Variety.Point (uVariety k n)) :
    IsUnit ((uPointMatrix n x).det : k) := by
  have hdet1 : (uPointMatrix n x).det = 1 := det_eq_one_of_uUnipotent n (uPoint_uUnipotent n x)
  rw [hdet1]
  exact isUnit_one

/-- Point equivalence for `Uₙ`. -/
@[expose]
public noncomputable def uPointEquiv (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) : Variety.Point (uVariety k n) ≃ uUnipotentGL k n := by
  refine ⟨fun x => ⟨Matrix.GeneralLinearGroup.mk'' (uPointMatrix n x) (uPoint_det_isUnit n x),
      (by
        change uUnipotent n (Matrix.GeneralLinearGroup.mk'' (uPointMatrix n x) (uPoint_det_isUnit n x)).1
        rw [show (Matrix.GeneralLinearGroup.mk'' (uPointMatrix n x) (uPoint_det_isUnit n x)).1 =
            uPointMatrix n x by rfl]
        exact uPoint_uUnipotent n x)⟩, fun A => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact fun p : ULift.{u} (Fin n × Fin n) => A.1.1 p.down.1 p.down.2
  · intro p hp
    rcases (Set.mem_ofPred.mp hp) with h | h
    · rcases h with ⟨i, j, hij, rfl⟩
      have htri : ∀ ⦃i j : Fin n⦄, j < i → A.1.1 i j = 0 := by
        simpa [uTriangular] using A.2.1
      have hz : A.1.1 i j = 0 := htri hij
      simp [evalPolynomial, hz]
    · rcases h with ⟨i, rfl⟩
      have hz : A.1.1 i i = 1 := A.2.2 i
      simp [evalPolynomial, hz]
  · intro x
    apply Variety.Point.ext
    funext p
    rfl
  · intro A
    apply Subtype.ext
    apply Units.ext
    ext i j
    rfl

/-- Matrix of coordinate variables for `Uₙ`. -/
public noncomputable def uEntryMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (ULift.{u} (Fin n × Fin n)) k) :=
  fun i j => MvPolynomial.X (ULift.up (i, j))

omit [IsAlgClosed k] in
/-- Evaluation of an adjugate entry. -/
public lemma evalPolynomial_uAdjugate (n : ℕ)
    (x : ULift.{u} (Fin n × Fin n) → k) (i j : Fin n) :
    evalPolynomial x ((Matrix.adjugate (uEntryMatrix n)) i j) =
      Matrix.adjugate (fun i' j' : Fin n => x (ULift.up (i', j'))) i j := by
  let M : Matrix (Fin n) (Fin n) k := fun i' j' => x (ULift.up (i', j'))
  change evalPolynomial x ((Matrix.adjugate (uEntryMatrix n)) i j) =
    Matrix.adjugate M i j
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  rw [Matrix.det_apply, Matrix.det_apply]
  simp_rw [Matrix.updateRow_apply]
  simp [evalPolynomial, uEntryMatrix, M, Pi.single,
    Function.update_apply, apply_ite]

/-- Multiplication polynomials for `Uₙ`. -/
@[expose]
public noncomputable def uMulPoly (n : ℕ) : (uVariety k n).Coordinates →
    MvPolynomial ((uVariety k n).Coordinates ⊕ (uVariety k n).Coordinates) k :=
  fun p => match p.down with
  | (i, j) =>
      ∑ l : Fin n, MvPolynomial.X (Sum.inl (ULift.up (i, l))) *
        MvPolynomial.X (Sum.inr (ULift.up (l, j)))

/-- Inverse polynomials for `Uₙ`, using Cramer's formula with determinant one. -/
@[expose]
public noncomputable def uInvPoly (n : ℕ) : (uVariety k n).Coordinates →
    MvPolynomial ((uVariety k n).Coordinates) k :=
  fun p => match p.down with
  | (i, j) => (Matrix.adjugate (uEntryMatrix n)) i j

public noncomputable instance uPointGroup (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) : Group (Variety.Point (uVariety k n)) :=
  (uPointEquiv (k := k) n).group

/-- `uPointEquiv` sends transported multiplication to matrix multiplication. -/
public lemma uPointEquiv_mul (n : ℕ)
    (x y : Variety.Point (uVariety k n)) :
    uPointEquiv k n (x * y) = uPointEquiv k n x * uPointEquiv k n y := by
  have h : x * y = (uPointEquiv k n).symm
      (uPointEquiv k n x * uPointEquiv k n y) := by rfl
  rw [h, Equiv.apply_symm_apply]

/-- `uPointEquiv` sends the transported identity to the matrix identity. -/
public lemma uPointEquiv_one (n : ℕ) :
    uPointEquiv k n (1 : Variety.Point (uVariety k n)) = 1 := by
  have h : (1 : Variety.Point (uVariety k n)) =
      (uPointEquiv k n).symm 1 := by rfl
  rw [h, Equiv.apply_symm_apply]

/-- A point reconstructed by `uPointEquiv` has the original matrix entry. -/
public lemma uPointEquiv_symm_val (n : ℕ) (A : uUnipotentGL k n)
    (q : ULift.{u} (Fin n × Fin n)) :
    ((uPointEquiv k n).symm A).val q = A.1.1 q.down.1 q.down.2 := rfl

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The algebraic-group structure on `Uₙ`. -/
public noncomputable instance uAlgebraicGroup (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) : AlgebraicGroup (uVariety k n) := by
  let e := uPointEquiv (k := k) n
  let hGroup : Group (Variety.Point (uVariety k n)) := e.group
  letI : Group (Variety.Point (uVariety k n)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := uMulPoly n
      invPolynomial := uInvPoly n
      mul_regular := by
        intro p x y
        rcases p with ⟨⟨i, j⟩⟩
        change (x * y).val (ULift.up (i, j)) = evalPolynomial (Sum.elim x.val y.val)
            (uMulPoly n (ULift.up (i, j)))
        simp [uMulPoly, evalPolynomial]
        change (e.symm (e x * e y)).val (ULift.up (i, j)) =
          ∑ l : Fin n, x.val (ULift.up (i, l)) * y.val (ULift.up (l, j))
        have hz : ∀ z : uUnipotentGL k n, (e.symm z).val (ULift.up (i, j)) = z.1.1 i j := by
          intro z
          rfl
        rw [hz]
        rfl
      inv_regular := by
        intro p x
        rcases p with ⟨⟨i, j⟩⟩
        change x⁻¹.val (ULift.up (i, j)) = evalPolynomial x.val (uInvPoly n (ULift.up (i, j)))
        rw [uInvPoly, evalPolynomial_uAdjugate]
        change (e.symm (e x)⁻¹).val (ULift.up (i, j)) =
          Matrix.adjugate (fun i' j' : Fin n => x.val (ULift.up (i', j'))) i j
        have hz : ∀ z : uUnipotentGL k n, (e.symm z).val (ULift.up (i, j)) = z.1.1 i j := by
          intro z
          rfl
        rw [hz]
        have hiv : ((e x)⁻¹ : uUnipotentGL k n).1.1 = Matrix.adjugate (uPointMatrix n x) := by
          have h1 : ((e x)⁻¹ : uUnipotentGL k n).1.1 = (uPointMatrix n x)⁻¹ := by
            simp
            rfl
          rw [h1]
          exact uUnipotent_inv_eq_adjugate n (uPoint_uUnipotent n x)
        rw [hiv]
        rfl }

end

section

open scoped commutatorElement

variable {k : Type u} [Field k]

private def Matrix.HasSuperdiagonalGap {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (r : ℕ) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < (i : ℕ) + r → A i j = 0

private lemma Matrix.HasSuperdiagonalGap.mono {n r s : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (hrs : r ≤ s)
    (hA : Matrix.HasSuperdiagonalGap A s) : Matrix.HasSuperdiagonalGap A r := by
  intro i j hij
  exact hA i j (hij.trans_le (Nat.add_le_add_left hrs i))

private lemma Matrix.HasSuperdiagonalGap.add {n r : ℕ}
    {A B : Matrix (Fin n) (Fin n) k}
    (hA : Matrix.HasSuperdiagonalGap A r) (hB : Matrix.HasSuperdiagonalGap B r) :
    Matrix.HasSuperdiagonalGap (A + B) r := by
  intro i j hij
  simp [hA i j hij, hB i j hij]

private lemma Matrix.HasSuperdiagonalGap.neg {n r : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (hA : Matrix.HasSuperdiagonalGap A r) :
    Matrix.HasSuperdiagonalGap (-A) r := by
  intro i j hij
  simp [hA i j hij]

private lemma Matrix.HasSuperdiagonalGap.mul {n r s : ℕ}
    {A B : Matrix (Fin n) (Fin n) k}
    (hA : Matrix.HasSuperdiagonalGap A r) (hB : Matrix.HasSuperdiagonalGap B s) :
    Matrix.HasSuperdiagonalGap (A * B) (r + s) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hil : (l : ℕ) < (i : ℕ) + r
  · rw [hA i l hil, zero_mul]
  · have hjl : (j : ℕ) < (l : ℕ) + s := by omega
    rw [hB l j hjl, mul_zero]

private lemma uUnipotent_sub_one_hasSuperdiagonalGap_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : uUnipotent n A) :
    Matrix.HasSuperdiagonalGap (A - 1) 0 := by
  intro i j hij
  have hji : j < i := by exact hij
  simp [Matrix.sub_apply, hA.1 hji, ne_of_gt hji]

private lemma uUnipotent_sub_one_hasSuperdiagonalGap_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : uUnipotent n A) :
    Matrix.HasSuperdiagonalGap (A - 1) 1 := by
  intro i j hij
  by_cases hji : j < i
  · simp [Matrix.sub_apply, hA.1 hji, ne_of_gt hji]
  · have hji' : j = i := by omega
    subst j
    simp [Matrix.sub_apply, hA.2]

variable [IsAlgClosed k]

private def uUnipotentGLSuperdiagonal (n r : ℕ) :
    Subgroup (uUnipotentGL k n) where
  carrier := {A | Matrix.HasSuperdiagonalGap (A.1.1 - 1) r}
  one_mem' := by
    intro i j _
    simp
  mul_mem' := by
    intro A B hA hB
    change Matrix.HasSuperdiagonalGap ((A * B).1.1 - 1) r
    have hmul : A.1.1 * B.1.1 - 1 =
        (A.1.1 - 1) + (B.1.1 - 1) + (A.1.1 - 1) * (B.1.1 - 1) := by
      noncomm_ring
    rw [show (A * B).1.1 = A.1.1 * B.1.1 by rfl, hmul]
    apply Matrix.HasSuperdiagonalGap.add (Matrix.HasSuperdiagonalGap.add hA hB)
    exact (Matrix.HasSuperdiagonalGap.mul hA hB).mono (Nat.le_add_right r r)
  inv_mem' := by
    intro A hA
    change Matrix.HasSuperdiagonalGap ((A⁻¹ : uUnipotentGL k n).1.1 - 1) r
    have hInvTri : Matrix.HasSuperdiagonalGap (A⁻¹ : uUnipotentGL k n).1.1 0 := by
      intro i j hij
      exact (A⁻¹ : uUnipotentGL k n).2.1 hij
    have hinv : (A⁻¹ : uUnipotentGL k n).1.1 - 1 =
        -(A.1.1 - 1) * (A⁻¹ : uUnipotentGL k n).1.1 := by
      have hunit : A.1.1 * (A⁻¹ : uUnipotentGL k n).1.1 = 1 := by
        simp
      calc
        (A⁻¹ : uUnipotentGL k n).1.1 - 1 =
            -(1 - (A⁻¹ : uUnipotentGL k n).1.1) := by abel
        _ = -((A.1.1 - 1) * (A⁻¹ : uUnipotentGL k n).1.1) := by
          rw [sub_mul, one_mul, hunit]
        _ = -(A.1.1 - 1) * (A⁻¹ : uUnipotentGL k n).1.1 := by
          rw [neg_mul]
    rw [hinv]
    simpa using Matrix.HasSuperdiagonalGap.mul hA.neg hInvTri

private lemma uUnipotentGLSuperdiagonal_zero (n : ℕ) :
    uUnipotentGLSuperdiagonal (k := k) n 0 = ⊤ := by
  apply eq_top_iff.mpr
  intro A _
  exact uUnipotent_sub_one_hasSuperdiagonalGap_zero A.1.1 A.2

private lemma uUnipotentGLSuperdiagonal_one (n : ℕ) :
    uUnipotentGLSuperdiagonal (k := k) n 1 = ⊤ := by
  apply eq_top_iff.mpr
  intro A _
  exact uUnipotent_sub_one_hasSuperdiagonalGap_one A.1.1 A.2

private lemma uUnipotentGLSuperdiagonal_antitone (n : ℕ) :
    Antitone (uUnipotentGLSuperdiagonal (k := k) n) := by
  intro r s hrs A hA
  exact hA.mono hrs

private lemma uUnipotentGL_commutator_mem_superdiagonal (n : ℕ) {r s : ℕ}
    {A B : uUnipotentGL k n}
    (hA : A ∈ uUnipotentGLSuperdiagonal n r)
    (hB : B ∈ uUnipotentGLSuperdiagonal n s) :
    ⁅A, B⁆ ∈ uUnipotentGLSuperdiagonal n (r + s) := by
  change Matrix.HasSuperdiagonalGap ((⁅A, B⁆ : uUnipotentGL k n).1.1 - 1) (r + s)
  have hInvA : Matrix.HasSuperdiagonalGap (A⁻¹ : uUnipotentGL k n).1.1 0 := by
    intro i j hij
    exact (A⁻¹ : uUnipotentGL k n).2.1 hij
  have hInvB : Matrix.HasSuperdiagonalGap (B⁻¹ : uUnipotentGL k n).1.1 0 := by
    intro i j hij
    exact (B⁻¹ : uUnipotentGL k n).2.1 hij
  have hsub : Matrix.HasSuperdiagonalGap (A.1.1 * B.1.1 - B.1.1 * A.1.1) (r + s) := by
    have hrewrite : A.1.1 * B.1.1 - B.1.1 * A.1.1 =
        (A.1.1 - 1) * (B.1.1 - 1) - (B.1.1 - 1) * (A.1.1 - 1) := by
      noncomm_ring
    rw [hrewrite]
    rw [sub_eq_add_neg]
    apply Matrix.HasSuperdiagonalGap.add (Matrix.HasSuperdiagonalGap.mul hA hB)
    simpa [Nat.add_comm] using (Matrix.HasSuperdiagonalGap.mul hB hA).neg
  have hunitA : A.1.1 * (A⁻¹ : uUnipotentGL k n).1.1 = 1 := by
    simp
  have hunitB : B.1.1 * (B⁻¹ : uUnipotentGL k n).1.1 = 1 := by
    simp
  have hcomm : ((⁅A, B⁆ : uUnipotentGL k n).1.1 - 1) =
      (A.1.1 * B.1.1 - B.1.1 * A.1.1) *
        (A⁻¹ : uUnipotentGL k n).1.1 * (B⁻¹ : uUnipotentGL k n).1.1 := by
    change A.1.1 * B.1.1 * (A⁻¹ : uUnipotentGL k n).1.1 *
        (B⁻¹ : uUnipotentGL k n).1.1 - 1 = _
    noncomm_ring [hunitA, hunitB]
  rw [hcomm]
  simpa using Matrix.HasSuperdiagonalGap.mul
    (Matrix.HasSuperdiagonalGap.mul hsub hInvA) hInvB

private lemma uUnipotentGLSuperdiagonal_commutator_le (n r s : ℕ) :
    ⁅uUnipotentGLSuperdiagonal (k := k) n r,
      uUnipotentGLSuperdiagonal (k := k) n s⁆ ≤
        uUnipotentGLSuperdiagonal (k := k) n (r + s) := by
  exact Subgroup.commutator_le.mpr fun _ hA _ hB =>
    uUnipotentGL_commutator_mem_superdiagonal n hA hB

private lemma uUnipotentGLSuperdiagonal_eq_bot (n : ℕ) :
    uUnipotentGLSuperdiagonal (k := k) n n = ⊥ := by
  apply le_antisymm
  · intro A hA
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Units.ext
    ext i j
    have hij : (j : ℕ) < (i : ℕ) + n :=
      j.isLt.trans_le (Nat.le_add_left n i)
    have hzero := hA i j hij
    exact sub_eq_zero.mp hzero
  · exact bot_le

public lemma uUnipotentGL_isNilpotent (n : ℕ) :
    Group.IsNilpotent (uUnipotentGL k n) := by
  apply (Subgroup.nilpotent_iff_finite_descending_central_series
    (uUnipotentGL k n)).mpr
  refine ⟨n, fun m => uUnipotentGLSuperdiagonal n (m + 1), ?_, ?_⟩
  · constructor
    · simpa using uUnipotentGLSuperdiagonal_one (k := k) n
    · intro A m hA B
      have hB : B ∈ uUnipotentGLSuperdiagonal (k := k) n 1 := by
        rw [uUnipotentGLSuperdiagonal_one]
        exact Subgroup.mem_top B
      simpa [Nat.add_assoc] using
        uUnipotentGL_commutator_mem_superdiagonal n hA hB
  · apply le_antisymm
    · exact (uUnipotentGLSuperdiagonal_antitone (k := k) n (Nat.le_succ n)).trans_eq
        (uUnipotentGLSuperdiagonal_eq_bot (k := k) n)
    · exact bot_le

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Override arbitrary matrix coordinates by zero below the diagonal and one
on the diagonal, producing a point of `U_n`. -/
private def uAffineParametrizationPoint (n : ℕ)
    (x : Variety.Point
      (affineSpaceVariety k (ULift.{u} (Fin n × Fin n)))) :
    Variety.Point (uVariety k n) where
  val := fun q =>
    if q.down.2 < q.down.1 then 0
    else if q.down.1 = q.down.2 then 1
    else x.val q
  isZero := by
    intro p hp
    rcases hp with ⟨i, j, hji, rfl⟩ | ⟨i, rfl⟩
    · simp [evalPolynomial, hji]
    · simp [evalPolynomial]

/-- Coordinate formula for the affine parametrization of `U_n`. -/
private lemma uAffineParametrizationPoint_val (n : ℕ)
    (x : Variety.Point
      (affineSpaceVariety k (ULift.{u} (Fin n × Fin n))))
    (q : ULift.{u} (Fin n × Fin n)) :
    (uAffineParametrizationPoint n x).val q =
      if q.down.2 < q.down.1 then 0
      else if q.down.1 = q.down.2 then 1
      else x.val q := rfl

/-- A polynomial surjection from matrix affine space onto `U_n`. -/
private def uAffineParametrization (n : ℕ) :
    Variety.Morphism
      (affineSpaceVariety k (ULift.{u} (Fin n × Fin n)))
      (uVariety k n) where
  toFun := uAffineParametrizationPoint n
  regular := by
    intro q
    by_cases hlt : q.down.2 < q.down.1
    · exact ⟨0, fun x => by
        rw [uAffineParametrizationPoint_val, if_pos hlt]
        simp [evalPolynomial]⟩
    · by_cases heq : q.down.1 = q.down.2
      · exact ⟨1, fun x => by
          rw [uAffineParametrizationPoint_val, if_neg hlt, if_pos heq]
          simp [evalPolynomial]⟩
      · exact ⟨MvPolynomial.X q, fun x => by
          rw [uAffineParametrizationPoint_val, if_neg hlt, if_neg heq]
          simp [evalPolynomial]⟩

/-- The affine parametrization has the point map used in its definition. -/
private lemma uAffineParametrization_apply (n : ℕ)
    (x : Variety.Point
      (affineSpaceVariety k (ULift.{u} (Fin n × Fin n)))) :
    (uAffineParametrization n).toFun x =
      uAffineParametrizationPoint n x := rfl

/-- The affine parametrization reaches every unitriangular point. -/
private lemma uAffineParametrization_surjective (n : ℕ) :
    Function.Surjective (uAffineParametrization (k := k) n).toFun := by
  intro y
  let x : Variety.Point
      (affineSpaceVariety k (ULift.{u} (Fin n × Fin n))) :=
    affineSpacePoint y.val
  refine ⟨x, ?_⟩
  rw [uAffineParametrization_apply]
  apply Variety.Point.ext
  funext q
  cases q with
  | up ij =>
      rcases ij with ⟨i, j⟩
      rw [uAffineParametrizationPoint_val]
      by_cases hji : j < i
      · rw [if_pos hji]
        exact (uPoint_uUnipotent n y).1 hji |>.symm
      · rw [if_neg hji]
        by_cases hij : i = j
        · rw [if_pos hij]
          subst j
          exact (uPoint_uUnipotent n y).2 i |>.symm
        · rw [if_neg hij]
          rfl

/-- The upper-unitriangular algebraic group is connected. -/
public lemma uVariety_isConnected (n : ℕ) :
    Variety.IsConnected (uVariety k n) := by
  let : ConnectedSpace (Variety.Point
      (affineSpaceVariety k (ULift.{u} (Fin n × Fin n)))) :=
    connectedSpace_iff_univ.mpr affineSpaceVariety_isConnected
  let : ConnectedSpace (Variety.Point (uVariety k n)) :=
    (uAffineParametrization_surjective (k := k) n).connectedSpace
      (uAffineParametrization n).continuous
  exact connectedSpace_iff_univ.mp inferInstance

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The strictly upper part of an upper-unitriangular `n × n` matrix has
nilpotence exponent at most `n`. -/
public lemma uUnipotent_sub_one_pow_eq_zero (n : ℕ)
    (A : Matrix (Fin n) (Fin n) k) (hA : uUnipotent n A) :
    (A - 1) ^ n = 0 := by
  have htri : A.BlockTriangular id := hA.1
  have hchar : A.charpoly = (Polynomial.X - Polynomial.C 1) ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular A htri]
    simp_rw [hA.2]
    simp
  have h := Matrix.aeval_self_charpoly A
  rw [hchar] at h
  simpa using h

omit [IsAlgClosed k] in
/-- In characteristic `p`, every upper-unitriangular `(n+1) × (n+1)`
matrix has order dividing `p^(n+1)`. -/
private lemma uUnipotent_pow_primePower_eq_one (p n : ℕ)
    [CharP k p] [Fact p.Prime]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (hA : uUnipotent (n + 1) A) :
    A ^ p ^ (n + 1) = 1 := by
  have hnil : (A - 1) ^ (n + 1) = 0 :=
    uUnipotent_sub_one_pow_eq_zero (n + 1) A hA
  have hle : n + 1 ≤ p ^ (n + 1) :=
    (Nat.le_of_lt (n + 1).lt_two_pow_self).trans (Nat.pow_le_pow_left
      (Nat.Prime.two_le (Fact.out : p.Prime)) (n + 1))
  have hnil' : (A - 1) ^ p ^ (n + 1) = 0 :=
    pow_eq_zero_of_le hle hnil
  let : Nonempty (Fin (n + 1)) :=
    Fin.pos_iff_nonempty.mp (Nat.zero_lt_succ n)
  let : FaithfulSMul k
      (Matrix (Fin (n + 1)) (Fin (n + 1)) k) := inferInstance
  let : ExpChar (Matrix (Fin (n + 1)) (Fin (n + 1)) k) p :=
    expChar_of_injective_algebraMap
      (R := k) (A := Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      (FaithfulSMul.algebraMap_injective k
        (Matrix (Fin (n + 1)) (Fin (n + 1)) k)) p
  have hcomm : Commute (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      (A - 1) := Commute.one_left _
  have hfrob := add_pow_expChar_pow_of_commute
    (R := Matrix (Fin (n + 1)) (Fin (n + 1)) k) p (n + 1) hcomm
  rw [show A = 1 + (A - 1) by
      calc
        A = (A - 1) + 1 := (sub_add_cancel A 1).symm
        _ = 1 + (A - 1) := add_comm _ _,
    hfrob, one_pow, hnil', add_zero]

/-- The point equivalence for `U_n` preserves natural powers. -/
private lemma uPointEquiv_pow (n : ℕ)
    (x : Variety.Point (uVariety k n)) (m : ℕ) :
    uPointEquiv k n (x ^ m) = (uPointEquiv k n x) ^ m := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero, uPointEquiv_one]
  | succ m ih =>
      rw [pow_succ, pow_succ, uPointEquiv_mul, ih]

/-- Every point of `U_n` has order dividing `p^n` in characteristic `p`. -/
public lemma uPoint_pow_primePower_eq_one (p n : ℕ)
    [CharP k p] [Fact p.Prime] (x : Variety.Point (uVariety k n)) :
    x ^ p ^ n = 1 := by
  cases n with
  | zero =>
      have hx : x = 1 := by
        apply Variety.Point.ext
        funext q
        exact Fin.elim0 q.down.1
      rw [hx, one_pow]
  | succ n =>
      apply (uPointEquiv k (n + 1)).injective
      rw [uPointEquiv_pow, uPointEquiv_one]
      apply Subtype.ext
      apply Units.ext
      change (uPointEquiv k (n + 1) x).1.1 ^ p ^ (n + 1) = 1
      exact uUnipotent_pow_primePower_eq_one p n
        (uPointEquiv k (n + 1) x).1.1
        (uPointEquiv k (n + 1) x).2

/-- In prime characteristic, the upper-unitriangular algebraic group is
unipotent. -/
public lemma uVariety_isUnipotentAlgebraicGroup (p n : ℕ)
    [CharP k p] [Fact p.Prime] :
    IsUnipotentAlgebraicGroup (uVariety k n) := by
  intro x
  exact pPowerOrder_implies_unipotent x p n
    (uPoint_pow_primePower_eq_one p n x)

/-- The ordinary subgroup inclusion from upper-unitriangular matrices into
upper-triangular invertible matrices. -/
@[expose]
public def uToTHom (n : ℕ) : uUnipotentGL k n →* tTriangularGL k n where
  toFun := fun A => ⟨A.1, A.2.1⟩
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- The matrix entries of the unitriangular inclusion are unchanged. -/
public lemma uToTHom_val (n : ℕ) (x : Variety.Point (uVariety k n))
    (i j : Fin n) :
    (uToTHom n (uPointEquiv k n x)).1.1 i j = uPointMatrix n x i j := rfl

/-- The regular closed-form inclusion `U_n → T_n`. -/
@[expose]
public noncomputable def uToTMorphism (n : ℕ) :
    AlgebraicGroup.Morphism (uVariety k n) (tVariety k n) where
  toVariety :=
    { toFun := fun x => (tPointEquiv k n).symm (uToTHom n (uPointEquiv k n x))
      regular := by
        intro p
        cases p with
        | inl q =>
            exact ⟨MvPolynomial.X (ULift.up q.down), fun x => by
              rw [tPointEquiv_symm_val_inl, uToTHom_val]
              simp [evalPolynomial, uPointMatrix]⟩
        | inr q =>
            exact ⟨MvPolynomial.C 1, fun x => by
              rw [tPointEquiv_symm_val_inr, uToTHom_val]
              rw [(uPoint_uUnipotent n x).2 q.down, inv_one]
              simp [evalPolynomial]⟩ }
  map_one := by
    apply (tPointEquiv k n).injective
    change tPointEquiv k n ((tPointEquiv k n).symm
      (uToTHom n (uPointEquiv k n 1))) = tPointEquiv k n 1
    rw [Equiv.apply_symm_apply, uPointEquiv_one, map_one, tPointEquiv_one]
  map_mul := by
    intro x y
    apply (tPointEquiv k n).injective
    change tPointEquiv k n ((tPointEquiv k n).symm
        (uToTHom n (uPointEquiv k n (x * y)))) =
      tPointEquiv k n
        ((tPointEquiv k n).symm (uToTHom n (uPointEquiv k n x)) *
          (tPointEquiv k n).symm (uToTHom n (uPointEquiv k n y)))
    rw [Equiv.apply_symm_apply, uPointEquiv_mul, map_mul, tPointEquiv_mul,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- On points, the regular inclusion `U_n → T_n` is the matrix-subgroup
inclusion transported through the point equivalences. -/
public lemma uToTMorphism_point (n : ℕ)
    (x : Variety.Point (uVariety k n)) :
    tPointEquiv k n ((uToTMorphism n).onPoints x) =
      uToTHom n (uPointEquiv k n x) := by
  change tPointEquiv k n ((tPointEquiv k n).symm
    (uToTHom n (uPointEquiv k n x))) = _
  exact Equiv.apply_symm_apply _ _

/-- The regular inclusion `U_n → T_n` preserves every matrix entry. -/
public lemma uToTMorphism_matrix (n : ℕ)
    (x : Variety.Point (uVariety k n)) (i j : Fin n) :
    tPointMatrix n ((uToTMorphism n).onPoints x) i j =
      uPointMatrix n x i j := by
  change ((uToTMorphism n).onPoints x).val
    (Sum.inl (ULift.up (i, j))) = uPointMatrix n x i j
  change ((tPointEquiv k n).symm
    (uToTHom n (uPointEquiv k n x))).val
      (Sum.inl (ULift.up (i, j))) = uPointMatrix n x i j
  rw [tPointEquiv_symm_val_inl, uToTHom_val]

/-- The image of `U_n → T_n` is exactly the kernel of the diagonal
projection `T_n → D_n`. -/
public lemma uToTMorphism_range_eq_kernel (n : ℕ) :
    Set.range (uToTMorphism (k := k) n).onPoints =
      ((tDiagonalMorphism (k := k) n).kernel :
        Set (Variety.Point (tVariety k n))) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    apply (tDiagonalMorphism_mem_kernel_iff n
      ((uToTMorphism n).onPoints x)).mpr
    intro i
    rw [uToTMorphism_matrix]
    exact (uPoint_uUnipotent n x).2 i
  · intro hy
    have hdiag : ∀ i : Fin n,
        (tPointEquiv k n y).1.1 i i = 1 := by
      intro i
      change tPointMatrix n y i i = 1
      exact (tDiagonalMorphism_mem_kernel_iff n y).mp hy i
    let U : uUnipotentGL k n :=
      ⟨(tPointEquiv k n y).1, ⟨(tPointEquiv k n y).2, hdiag⟩⟩
    let x : Variety.Point (uVariety k n) := (uPointEquiv k n).symm U
    refine ⟨x, ?_⟩
    apply (tPointEquiv k n).injective
    rw [uToTMorphism_point]
    rw [show uPointEquiv k n x = U by exact Equiv.apply_symm_apply _ _]
    apply Subtype.ext
    rfl

/-- The point map from `U_n` to the carrier variety of the diagonal kernel. -/
@[expose]
public noncomputable def uToTKernelPoint (n : ℕ)
    (x : Variety.Point (uVariety k n)) :
    Variety.Point (tUnipotentKernel (k := k) n).carrierVariety :=
  (tUnipotentKernel n).pointEquiv.symm
    ⟨(uToTMorphism n).onPoints x, by
      have hx : (uToTMorphism n).onPoints x ∈
          Set.range (uToTMorphism n).onPoints := ⟨x, rfl⟩
      rw [uToTMorphism_range_eq_kernel] at hx
      exact hx⟩

/-- Forgetting the kernel certificate recovers the standard inclusion
`U_n → T_n`. -/
public lemma uToTKernelPoint_val (n : ℕ)
    (x : Variety.Point (uVariety k n)) :
    ((tUnipotentKernel n).pointEquiv (uToTKernelPoint n x)).val =
      (uToTMorphism n).onPoints x := by
  change ((tUnipotentKernel n).pointEquiv
    ((tUnipotentKernel n).pointEquiv.symm _)).val = _
  rw [Equiv.apply_symm_apply]

/-- The regular inclusion of `U_n` into the carrier variety of the diagonal
kernel. -/
@[expose]
public noncomputable def uToTKernelMorphism (n : ℕ) :
    AlgebraicGroup.Morphism (uVariety k n)
      (tUnipotentKernel (k := k) n).carrierVariety where
  toVariety :=
    { toFun := uToTKernelPoint (k := k) n
      regular := by
        intro p
        rcases (uToTMorphism (k := k) n).toVariety.regular p with ⟨q, hq⟩
        exact ⟨q, fun x => by
          change ((tUnipotentKernel n).pointEquiv
            (uToTKernelPoint (k := k) n x)).val.val p = evalPolynomial x.val q
          rw [uToTKernelPoint_val (k := k)]
          exact hq x⟩ }
  map_one := by
    apply (tUnipotentKernel n).pointEquiv.injective
    apply Subtype.ext
    rw [uToTKernelPoint_val (k := k)]
    exact (uToTMorphism (k := k) n).map_one
  map_mul := by
    intro x y
    apply (tUnipotentKernel n).pointEquiv.injective
    apply Subtype.ext
    change (uToTMorphism (k := k) n).onPoints (x * y) =
      ((tUnipotentKernel n).pointEquiv
          (uToTKernelPoint (k := k) n x)).val *
        ((tUnipotentKernel n).pointEquiv
          (uToTKernelPoint (k := k) n y)).val
    rw [uToTKernelPoint_val (k := k), uToTKernelPoint_val (k := k)]
    exact (uToTMorphism (k := k) n).map_mul x y

/-- Recover the corresponding `U_n` point from a point of the diagonal
kernel. -/
@[expose]
public noncomputable def tKernelToUPoint (n : ℕ)
    (z : Variety.Point (tUnipotentKernel (k := k) n).carrierVariety) :
    Variety.Point (uVariety k n) := by
  let y := (tUnipotentKernel n).inclusion.onPoints z
  have hy : y ∈ (tDiagonalMorphism n).kernel := by
    change ((tUnipotentKernel n).pointEquiv z).val ∈
      (tDiagonalMorphism n).kernel
    exact (tUnipotentKernel n).pointEquiv z |>.property
  have hdiag : ∀ i : Fin n, (tPointEquiv k n y).1.1 i i = 1 := by
    intro i
    change tPointMatrix n y i i = 1
    exact (tDiagonalMorphism_mem_kernel_iff n y).mp hy i
  let U : uUnipotentGL k n :=
    ⟨(tPointEquiv k n y).1, ⟨(tPointEquiv k n y).2, hdiag⟩⟩
  exact (uPointEquiv k n).symm U

/-- Recovering a unitriangular point retains each ambient matrix-entry
coordinate of the kernel point. -/
public lemma tKernelToUPoint_val (n : ℕ)
    (z : Variety.Point (tUnipotentKernel (k := k) n).carrierVariety)
    (q : ULift.{u} (Fin n × Fin n)) :
    (tKernelToUPoint n z).val q =
      ((tUnipotentKernel n).pointEquiv z).val.val (Sum.inl q) := by
  rfl

/-- Recovering a unitriangular point after inserting it into the diagonal
kernel is the identity. -/
public lemma tKernelToUPoint_uToTKernelMorphism (n : ℕ)
    (x : Variety.Point (uVariety k n)) :
    tKernelToUPoint n ((uToTKernelMorphism n).onPoints x) = x := by
  apply (uPointEquiv k n).injective
  apply Subtype.ext
  rfl

/-- Inserting the unitriangular point recovered from a diagonal-kernel point
is the identity. -/
public lemma uToTKernelMorphism_tKernelToUPoint (n : ℕ)
    (z : Variety.Point (tUnipotentKernel (k := k) n).carrierVariety) :
    (uToTKernelMorphism n).onPoints (tKernelToUPoint n z) = z := by
  apply (tUnipotentKernel n).pointEquiv.injective
  apply Subtype.ext
  change (uToTMorphism n).onPoints (tKernelToUPoint n z) = _
  apply (tPointEquiv k n).injective
  apply Subtype.ext
  rfl

/-- The regular inverse from the carrier of the diagonal kernel to `U_n`. -/
@[expose]
public noncomputable def tKernelToUMorphism (n : ℕ) :
    AlgebraicGroup.Morphism
      (tUnipotentKernel (k := k) n).carrierVariety (uVariety k n) where
  toVariety :=
    { toFun := tKernelToUPoint n
      regular := by
        intro q
        exact ⟨MvPolynomial.X (Sum.inl q), fun z => by
          rw [tKernelToUPoint_val, ClosedSubgroup.pointEquiv_val]
          simp [evalPolynomial]⟩ }
  map_one := by
    have hinj : Function.Injective
        (uToTKernelMorphism (k := k) n).onPoints := by
      intro x y hxy
      rw [← tKernelToUPoint_uToTKernelMorphism n x,
        ← tKernelToUPoint_uToTKernelMorphism n y, hxy]
    apply hinj
    rw [uToTKernelMorphism_tKernelToUPoint]
    exact (uToTKernelMorphism n).map_one.symm
  map_mul := by
    intro x y
    have hinj : Function.Injective
        (uToTKernelMorphism (k := k) n).onPoints := by
      intro a b hab
      rw [← tKernelToUPoint_uToTKernelMorphism n a,
        ← tKernelToUPoint_uToTKernelMorphism n b, hab]
    apply hinj
    rw [uToTKernelMorphism_tKernelToUPoint]
    calc
      x * y =
          (uToTKernelMorphism n).onPoints (tKernelToUPoint n x) *
            (uToTKernelMorphism n).onPoints (tKernelToUPoint n y) := by
        rw [uToTKernelMorphism_tKernelToUPoint,
          uToTKernelMorphism_tKernelToUPoint]
      _ = (uToTKernelMorphism n).onPoints
          (tKernelToUPoint n x * tKernelToUPoint n y) :=
        ((uToTKernelMorphism n).map_mul _ _).symm

/-- The unitriangular algebraic group is the closed kernel of the diagonal
projection from the upper-triangular group. -/
@[expose]
public noncomputable def uVarietyIsoTUnipotentKernel (n : ℕ) :
    AlgebraicGroup.Iso (uVariety k n)
      (tUnipotentKernel (k := k) n).carrierVariety where
  hom := uToTKernelMorphism n
  inv := tKernelToUMorphism n
  hom_inv_id := tKernelToUPoint_uToTKernelMorphism n
  inv_hom_id := uToTKernelMorphism_tKernelToUPoint n

omit [IsAlgClosed k] in
/-- Iterates of a linear map preserve addition. -/
private lemma iterate_map_add
    {A : Type*} [AddCommGroup A] [Module k A]
    (D : A →ₗ[k] A) :
    ∀ n (x y : A), (D^[n]) (x + y) = (D^[n]) x + (D^[n]) y := by
  intro n
  induction n with
  | zero => intro x y; rfl
  | succ n ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]

omit [IsAlgClosed k] in
/-- Two vectors killed by the same iterate have a sum killed by that
iterate. -/
private lemma locallyKilled_add
    {A : Type*} [AddCommGroup A] [Module k A]
    (D : A →ₗ[k] A) {x y : A} {n : ℕ}
    (hx : (D^[n]) x = 0) (hy : (D^[n]) y = 0) :
    (D^[n]) (x + y) = 0 := by
  rw [iterate_map_add D n x y, hx, hy, add_zero]

omit [IsAlgClosed k] in
/-- Iterates inherit commutation with another linear map. -/
private lemma iterate_commute
    {A : Type*} [AddCommGroup A] [Module k A]
    (D T : A →ₗ[k] A) (hcomm : D.comp T = T.comp D) :
    ∀ n x, (D^[n]) (T x) = T ((D^[n]) x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact LinearMap.congr_fun hcomm ((D^[n]) x)

omit [IsAlgClosed k] in
/-- Local nilpotence of a multiplicative linear operator is preserved under
products. -/
private lemma locallyKilled_mul
    {A : Type*} [CommRing A] [Algebra k A]
    (T : A →ₗ[k] A)
    (hmul : ∀ x y, T (x * y) = T x * T y)
    (x y : A) (m n : ℕ)
    (hx : (((T - 1 : A →ₗ[k] A))^[m]) x = 0)
    (hy : (((T - 1 : A →ₗ[k] A))^[n]) y = 0) :
    (((T - 1 : A →ₗ[k] A))^[m + n]) (x * y) = 0 := by
  let D : A →ₗ[k] A := T - 1
  change (D^[m]) x = 0 at hx
  change (D^[n]) y = 0 at hy
  change (D^[m + n]) (x * y) = 0
  have hDmul (a b : A) : D (a * b) = D a * T b + a * D b := by
    change T (a * b) - a * b = (T a - a) * T b + a * (T b - b)
    rw [hmul]
    ring
  have hcomm : D.comp T = T.comp D := by
    apply LinearMap.ext
    intro a
    change T (T a) - T a = T (T a - a)
    simp
  induction m generalizing x y n with
  | zero =>
      simp only [Function.iterate_zero, id_eq] at hx
      simp [hx]
  | succ m ihm =>
      induction n generalizing x y with
      | zero =>
          simp only [Function.iterate_zero, id_eq] at hy
          simp [hy]
      | succ n ihn =>
          rw [show Nat.succ m + Nat.succ n = Nat.succ (m + Nat.succ n) by omega,
            Function.iterate_succ_apply, hDmul]
          have hx' : (D^[m]) (D x) = 0 := by
            simpa [Function.iterate_succ_apply] using hx
          have hyT : (D^[Nat.succ n]) (T y) = 0 := by
            rw [iterate_commute D T hcomm, hy, map_zero]
          have hfirst : (D^[m + Nat.succ n]) (D x * T y) = 0 :=
            ihm (D x) (T y) (Nat.succ n) hx' hyT
          have hy' : (D^[n]) (D y) = 0 := by
            simpa [Function.iterate_succ_apply] using hy
          have hsecond : (D^[Nat.succ m + n]) (x * D y) = 0 :=
            ihn x (D y) hx hy'
          rw [← show m + Nat.succ n = Nat.succ m + n by omega] at hsecond
          exact locallyKilled_add D hfirst hsecond

/-- Matrix coordinates of `U_n` points preserve multiplication. -/
private lemma uPointMatrix_mul (n : ℕ)
    (x y : Variety.Point (uVariety k n)) :
    uPointMatrix n (x * y) = uPointMatrix n x * uPointMatrix n y := by
  apply Matrix.ext
  intro i j
  have h := congrArg (fun A : uUnipotentGL k n => A.1.1 i j)
    (uPointEquiv_mul n x y)
  exact h

/-- Iterated translation differences of a coordinate are matrix powers of
the strictly upper-triangular part. -/
private lemma uCoordinate_iterate_sub_rightTranslation (n : ℕ)
    (g : Variety.Point (uVariety k n)) (i j : Fin n) :
    ∀ m : ℕ, ∀ x : Variety.Point (uVariety k n),
      (((rightTranslationPullback (uVariety k n) g - 1 :
          Variety.PolynomialFunction (uVariety k n) →ₗ[k]
            Variety.PolynomialFunction (uVariety k n))^[m])
        (Variety.PolynomialFunction.ofPolynomial (uVariety k n)
          (MvPolynomial.X (ULift.up (i, j))))) x =
      (uPointMatrix n x * (uPointMatrix n g - 1) ^ m) i j := by
  intro m
  induction m with
  | zero =>
      intro x
      simp [Variety.PolynomialFunction.ofPolynomial,
        Variety.PolynomialFunction.toFun, evalPolynomial, uPointMatrix]
  | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply']
      let F :=
        (((rightTranslationPullback (uVariety k n) g - 1 :
            Variety.PolynomialFunction (uVariety k n) →ₗ[k]
              Variety.PolynomialFunction (uVariety k n))^[m])
          (Variety.PolynomialFunction.ofPolynomial (uVariety k n)
            (MvPolynomial.X (ULift.up (i, j)))))
      change (rightTranslationPullback (uVariety k n) g F) x - F x = _
      rw [rightTranslationPullback_apply, ih, ih, uPointMatrix_mul]
      have hmatrix :
          uPointMatrix n x * uPointMatrix n g * (uPointMatrix n g - 1) ^ m -
              uPointMatrix n x * (uPointMatrix n g - 1) ^ m =
            uPointMatrix n x * (uPointMatrix n g - 1) ^ (m + 1) := by
        rw [pow_succ']
        noncomm_ring
      exact congrFun (congrFun hmatrix i) j

/-- Every upper-unitriangular algebraic group is unipotent, in arbitrary
characteristic. -/
public theorem uVariety_isUnipotentAlgebraicGroup_characteristicFree (n : ℕ) :
    IsUnipotentAlgebraicGroup (uVariety k n) := by
  intro g
  simp only [IsUnipotentElement]
  intro f
  let T : Variety.PolynomialFunction (uVariety k n) →ₗ[k]
      Variety.PolynomialFunction (uVariety k n) :=
    rightTranslationPullback (uVariety k n) g
  have hmul (a b : Variety.PolynomialFunction (uVariety k n)) :
      T (a * b) = T a * T b := by
    apply Variety.PolynomialFunction.ext
    intro x
    change (a * b) (x * g) = (T a) x * (T b) x
    rw [show T a x = a (x * g) by simp [T, rightTranslationPullback_apply]]
    rw [show T b x = b (x * g) by simp [T, rightTranslationPullback_apply]]
    rfl
  have hcoordinate (q : (uVariety k n).Coordinates) :
      (((T - 1 : Variety.PolynomialFunction (uVariety k n) →ₗ[k]
        Variety.PolynomialFunction (uVariety k n)))^[n])
        (Variety.PolynomialFunction.ofPolynomial (uVariety k n)
          (MvPolynomial.X q)) = 0 := by
    rcases q with ⟨⟨i, j⟩⟩
    apply Variety.PolynomialFunction.ext
    intro x
    rw [uCoordinate_iterate_sub_rightTranslation n g i j n x]
    rw [uUnipotent_sub_one_pow_eq_zero n (uPointMatrix n g)
      (uPoint_uUnipotent n g)]
    simp
  rcases f.representedBy with ⟨p, hp⟩
  have hpoly : ∀ p : MvPolynomial (uVariety k n).Coordinates k,
      ∃ r : ℕ, (((T - 1 : Variety.PolynomialFunction (uVariety k n) →ₗ[k]
        Variety.PolynomialFunction (uVariety k n)))^[r])
        (Variety.PolynomialFunction.ofPolynomial (uVariety k n) p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        refine ⟨1, ?_⟩
        apply Variety.PolynomialFunction.ext
        intro x
        change T (Variety.PolynomialFunction.ofPolynomial (uVariety k n)
          (MvPolynomial.C a)) x -
            Variety.PolynomialFunction.ofPolynomial (uVariety k n)
              (MvPolynomial.C a) x = 0
        rw [show T (Variety.PolynomialFunction.ofPolynomial (uVariety k n)
          (MvPolynomial.C a)) x =
            Variety.PolynomialFunction.ofPolynomial (uVariety k n)
              (MvPolynomial.C a) (x * g) by
          simp [T, rightTranslationPullback_apply]]
        simp [Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, evalPolynomial]
    | add p q hp hq =>
        rcases hp with ⟨m, hm⟩
        rcases hq with ⟨r, hr⟩
        refine ⟨m + r, ?_⟩
        have hm' : (((T - 1 : Variety.PolynomialFunction (uVariety k n) →ₗ[k]
            Variety.PolynomialFunction (uVariety k n)))^[m + r])
            (Variety.PolynomialFunction.ofPolynomial (uVariety k n) p) = 0 := by
          rw [Nat.add_comm, Function.iterate_add_apply, hm]
          simp
        have hr' : (((T - 1 : Variety.PolynomialFunction (uVariety k n) →ₗ[k]
            Variety.PolynomialFunction (uVariety k n)))^[m + r])
            (Variety.PolynomialFunction.ofPolynomial (uVariety k n) q) = 0 := by
          rw [Function.iterate_add_apply, hr]
          simp
        rw [show Variety.PolynomialFunction.ofPolynomial (uVariety k n) (p + q) =
            Variety.PolynomialFunction.ofPolynomial (uVariety k n) p +
              Variety.PolynomialFunction.ofPolynomial (uVariety k n) q by
          apply Variety.PolynomialFunction.ext
          intro x
          simp [Variety.PolynomialFunction.ofPolynomial,
            Variety.PolynomialFunction.toFun, evalPolynomial]]
        exact locallyKilled_add (T - 1) hm' hr'
    | mul_X p q hp =>
        rcases hp with ⟨m, hm⟩
        refine ⟨m + n, ?_⟩
        rw [show Variety.PolynomialFunction.ofPolynomial (uVariety k n)
            (p * MvPolynomial.X q) =
              Variety.PolynomialFunction.ofPolynomial (uVariety k n) p *
                Variety.PolynomialFunction.ofPolynomial (uVariety k n)
                  (MvPolynomial.X q) by
          apply Variety.PolynomialFunction.ext
          intro x
          simp [Variety.PolynomialFunction.ofPolynomial,
            Variety.PolynomialFunction.toFun, evalPolynomial]]
        exact locallyKilled_mul T hmul
          (Variety.PolynomialFunction.ofPolynomial (uVariety k n) p)
          (Variety.PolynomialFunction.ofPolynomial (uVariety k n)
            (MvPolynomial.X q))
          m n hm (hcoordinate q)
  rcases hpoly p with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  have hfeq : f = Variety.PolynomialFunction.ofPolynomial (uVariety k n) p := by
    apply Variety.PolynomialFunction.ext
    exact hp
  rw [hfeq]
  exact hr

end

end Theory.AlgebraicGroup
