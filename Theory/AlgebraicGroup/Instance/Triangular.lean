module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Instance.Diagonal

universe u

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def tTriangular (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ ⦃i j : Fin n⦄, j < i → A i j = 0

omit [IsAlgClosed k] in
/-- Upper-triangular matrices are closed under multiplication. -/
public lemma tTriangular_mul (n : ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : tTriangular n A) (hB : tTriangular n B) : tTriangular n (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hli : l < i
  · rw [hA hli, zero_mul]
  · -- l ≥ i > j ⟹ j < l ⟹ B l j = 0
    have hjl : j < l := lt_of_lt_of_le hij (le_of_not_gt hli)
    rw [hB hjl, mul_zero]

/-- A permutation satisfying `σ i ≤ i` for every `i` is the identity. -/
public lemma tPerm_eq_id_of_le (n : ℕ) (σ : Equiv.Perm (Fin n))
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
public lemma det_eq_prod_diagonal_of_tTriangular (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : tTriangular n A) : A.det = ∏ i : Fin n, A i i := by
  rw [Matrix.det_apply]
  -- Only the identity permutation contributes: a nonzero term requires
  -- `σ l ≤ l` for all `l`, while upper triangularity gives `l ≤ σ l`.
  have hmem : ∀ σ : Equiv.Perm (Fin n), σ ≠ 1 → (Equiv.Perm.sign σ) • (∏ i, A (σ i) i) = 0 := by
    intro σ hσ
    have hle : ∃ i : Fin n, i < σ i := by
      by_contra h'
      apply hσ
      exact tPerm_eq_id_of_le n σ (by
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
/-- The adjugate of an upper-triangular matrix is upper triangular. -/
public lemma tAdjugate_upperTriangular (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : tTriangular n A) ⦃i j : Fin n⦄ (hij : j < i) : (Matrix.adjugate A) i j = 0 := by
  rw [Matrix.adjugate_apply]
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  -- Locate a zero factor in the product.
  by_cases hσid : σ = 1
  · -- For `σ = id`, the factor in column `j` is zero because `i ≠ j`.
    have hne : i ≠ j := ne_of_gt hij
    have hprod : (∏ l : Fin n, (A.updateRow j (Pi.single i 1)) (σ l) l) = 0 := by
      rw [hσid]
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by
        simp [Matrix.updateRow_apply, Pi.single, Ne.symm hne])]
    simp [hprod]
  · -- For `σ ≠ id`, choose an ascent `l < σ l`; the factor in column `l` is zero.
    have hup : ∃ l : Fin n, l < σ l := by
      by_contra h'
      apply hσid
      exact tPerm_eq_id_of_le n σ (by
        intro l
        exact le_of_not_gt (by intro h; exact h' ⟨l, h⟩))
    rcases hup with ⟨l, hl⟩
    by_cases hσl : σ l = j
    · -- M(σ l, l) = M(j, l) = single i 1 l = 0（l ≠ i）
      have hli : l ≠ i := by
        intro hli
        subst hli
        exact (not_lt_of_ge (le_of_lt hij)) (by simpa [hσl] using hl)
      have hprod : (∏ t : Fin n, (A.updateRow j (Pi.single i 1)) (σ t) t) = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ l) (by
          simp [hσl, Matrix.updateRow_apply, Pi.single, hli])]
      simp [hprod]
    · -- `M (σ l) l = A (σ l) l = 0` by upper triangularity.
      have hz : A (σ l) l = 0 := hA (i := σ l) (j := l) hl
      have hprod : (∏ t : Fin n, (A.updateRow j (Pi.single i 1)) (σ t) t) = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ l) (by
          simp [Matrix.updateRow_apply, hσl, hz])]
      simp [hprod]

omit [IsAlgClosed k] in
/-- The inverse of an invertible upper-triangular matrix is upper triangular. -/
public lemma tTriangular_inv (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : tTriangular n A) (hdet : IsUnit A.det) : tTriangular n A⁻¹ := by
  rw [Matrix.nonsing_inv_apply (A := A) hdet]
  intro i j hij
  change (↑hdet.unit⁻¹ : k) • (Matrix.adjugate A) i j = 0
  rw [tAdjugate_upperTriangular n hA hij]
  simp

/-- The upper-triangular matrices form a subgroup of `GLₙ`. -/
@[expose]
public def tTriangularGL (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    Subgroup (GL (Fin n) k) where
  carrier := {g : GL (Fin n) k | tTriangular n g.1}
  one_mem' := by
    intro i j hij
    simpa [Matrix.one_apply] using (ne_of_gt hij)
  mul_mem' := by
    intro a b ha hb
    change tTriangular n (a : Matrix (Fin n) (Fin n) k) at ha
    change tTriangular n (b : Matrix (Fin n) (Fin n) k) at hb
    exact tTriangular_mul n ha hb
  inv_mem' := by
    intro a ha
    change tTriangular n ((a⁻¹ : GL (Fin n) k).1)
    change tTriangular n (a : Matrix (Fin n) (Fin n) k) at ha
    have hgl : (a⁻¹ : GL (Fin n) k).1 = a.1⁻¹ := by
      exact (Units.inv_eq_of_mul_eq_one_right (u := a) (a := a.1⁻¹) (by
        exact Matrix.mul_nonsing_inv a.1 (a.isUnit.map Matrix.detMonoidHom)))
    rw [hgl]
    exact tTriangular_inv n ha (a.isUnit.map Matrix.detMonoidHom)

/-- Affine equations for `Tₙ`: upper triangularity and diagonal times inverse equal to one. -/
public abbrev tVariety (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) : Variety k where
  Coordinates := ULift.{u} (Fin n × Fin n) ⊕ ULift.{u} (Fin n)
  finiteCoordinates := inferInstance
  equations : Set (MvPolynomial (ULift.{u} (Fin n × Fin n) ⊕ ULift.{u} (Fin n)) k) :=
    {p | (∃ i j : Fin n, j < i ∧ p = MvPolynomial.X (Sum.inl (ULift.up (i, j)))) ∨
         (∃ i : Fin n, p = MvPolynomial.X (Sum.inl (ULift.up (i, i))) *
            MvPolynomial.X (Sum.inr (ULift.up i)) - 1)}

/-- Matrix component of a `Tₙ` point. -/
@[expose]
public def tPointMatrix (n : ℕ) (x : Variety.Point (tVariety k n)) :
    Matrix (Fin n) (Fin n) k :=
  fun i j => x.val (Sum.inl (ULift.up (i, j)))

/-- Inverse-determinant coordinate of a `Tₙ` point. -/
@[expose]
public def tPointD (n : ℕ) (x : Variety.Point (tVariety k n)) (i : Fin n) : k :=
  x.val (Sum.inr (ULift.up i))

/-- A `Tₙ` point satisfies the upper-triangular conditions. -/
public lemma tPoint_triangular (n : ℕ) (x : Variety.Point (tVariety k n)) :
    tTriangular n (tPointMatrix n x) := by
  intro i j hij
  have h := x.isZero (MvPolynomial.X (Sum.inl (ULift.up (i, j)))) (by
    exact Set.mem_ofPred.mpr (Or.inl ⟨i, j, hij, rfl⟩))
  simpa [tPointMatrix, evalPolynomial] using h

/-- Diagonal and inverse coordinates of a `Tₙ` point multiply to one. -/
public lemma tPoint_diag_mul_inv (n : ℕ) (x : Variety.Point (tVariety k n)) (i : Fin n) :
    tPointMatrix n x i i * tPointD n x i = 1 := by
  have h := x.isZero (MvPolynomial.X (Sum.inl (ULift.up (i, i))) *
      MvPolynomial.X (Sum.inr (ULift.up i)) - 1) (by
    exact Set.mem_ofPred.mpr (Or.inr ⟨i, rfl⟩))
  have hsum : evalPolynomial x.val (MvPolynomial.X (Sum.inl (ULift.up (i, i)))) *
      evalPolynomial x.val (MvPolynomial.X (Sum.inr (ULift.up i))) - 1 = 0 := by
    simpa [evalPolynomial, evalPolynomial_mul] using h
  simpa [tPointMatrix, tPointD, evalPolynomial, evalPolynomial_X] using (sub_eq_zero.mp hsum)

/-- The determinant of a `Tₙ` point is a unit. -/
public lemma tPoint_det_isUnit (n : ℕ) (x : Variety.Point (tVariety k n)) :
    IsUnit ((tPointMatrix n x).det : k) := by
  have hdiag : ∀ i : Fin n, IsUnit (tPointMatrix n x i i) := by
    intro i
    exact IsUnit.of_mul_eq_one (tPointD n x i) (tPoint_diag_mul_inv n x i)
  have hdet : (tPointMatrix n x).det = ∏ i : Fin n, tPointMatrix n x i i :=
    det_eq_prod_diagonal_of_tTriangular n (tPoint_triangular n x)
  rw [hdet]
  apply IsUnit.mk0
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact IsUnit.ne_zero (hdiag i)

/-- Diagonal entries of a `Tₙ` matrix are units. -/
public lemma tDiagIsUnit (n : ℕ) (A : tTriangularGL k n) (i : Fin n) :
    IsUnit (A.1.1 i i) := by
  apply IsUnit.mk0
  have hdet1 : A.1.1.det ≠ 0 := IsUnit.ne_zero ((A.1).isUnit.map Matrix.detMonoidHom)
  have hprod : (∏ l : Fin n, A.1.1 l l) ≠ 0 := by
    rw [← det_eq_prod_diagonal_of_tTriangular n A.2]
    exact hdet1
  exact Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ _)

/-- The point corresponding to an upper-triangular `GLₙ` matrix. -/
@[expose]
public def tPointOfGL (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (A : tTriangularGL k n) : Variety.Point (tVariety k n) :=
  ⟨fun p => match p with
    | Sum.inl q => A.1.1 q.down.1 q.down.2
    | Sum.inr q => (A.1.1 q.down q.down)⁻¹,
    by
      intro p hp
      rcases (Set.mem_ofPred.mp hp) with h | h
      · rcases h with ⟨i, j, hij, rfl⟩
        have hz : A.1.1 i j = 0 := A.2 hij
        simp [evalPolynomial, hz]
      · rcases h with ⟨i, rfl⟩
        have hne : A.1.1 i i ≠ 0 := IsUnit.ne_zero (tDiagIsUnit n A i)
        simp [evalPolynomial, mul_inv_cancel₀ hne]⟩

/-- The upper-triangular `GLₙ` matrix corresponding to a point. -/
@[expose]
public noncomputable def tGLOfPoint (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (x : Variety.Point (tVariety k n)) : tTriangularGL k n :=
  ⟨Matrix.GeneralLinearGroup.mk'' (tPointMatrix n x) (tPoint_det_isUnit n x), by
    change tTriangular n (Matrix.GeneralLinearGroup.mk'' (tPointMatrix n x) (tPoint_det_isUnit n x)).1
    rw [show (Matrix.GeneralLinearGroup.mk'' (tPointMatrix n x) (tPoint_det_isUnit n x)).1 =
        tPointMatrix n x by rfl]
    exact tPoint_triangular n x⟩

/-- Point equivalence for `Tₙ`. -/
@[expose]
public noncomputable def tPointEquiv (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    Variety.Point (tVariety k n) ≃ tTriangularGL k n :=
  ⟨tGLOfPoint k n, tPointOfGL k n,
    by
      intro x
      apply Variety.Point.ext
      funext p
      cases p with
      | inl q => rfl
      | inr q =>
        change (tPointMatrix n x q.down q.down)⁻¹ = tPointD n x q.down
        exact (eq_inv_of_mul_eq_one_right (tPoint_diag_mul_inv n x q.down)).symm,
    by
      intro A
      apply Subtype.ext
      apply Units.ext
      ext i j
      change tPointMatrix n (tPointOfGL k n A) i j = A.1.1 i j
      simp [tPointMatrix, tPointOfGL]⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The diagonal of a product of upper-triangular matrices is the product of
the diagonal entries. -/
public lemma tTriangular_mul_apply_diag (n : ℕ)
    {A B : Matrix (Fin n) (Fin n) k}
    (hA : tTriangular n A) (hB : tTriangular n B) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro l _ hli
    by_cases hlt : l < i
    · rw [hA hlt, zero_mul]
    · have hil : i < l := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hli)
      rw [hB hil, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

public noncomputable def tEntryMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (tVariety k n).Coordinates k) :=
  fun i j => MvPolynomial.X (Sum.inl (ULift.up (i, j)))

private lemma evalPolynomial_tAdjugate (n : ℕ)
    (x : (tVariety k n).Coordinates → k) (i j : Fin n) :
    evalPolynomial x ((Matrix.adjugate (tEntryMatrix n)) i j) =
      Matrix.adjugate
        (Matrix.of (fun i' j' : Fin n => x (Sum.inl (ULift.up (i', j'))))) i j := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  rw [Matrix.det_apply, Matrix.det_apply]
  simp [evalPolynomial, tEntryMatrix, Matrix.updateRow_apply, Pi.single,
    Function.update_apply, apply_ite]

/-- Inverting an invertible upper-triangular matrix inverts each diagonal
entry. -/
public lemma tTriangularGL_inv_diag (n : ℕ) (A : tTriangularGL k n)
    (i : Fin n) :
    ((A⁻¹ : tTriangularGL k n).1.1 i i) = (A.1.1 i i)⁻¹ := by
  have hsub : (A⁻¹ * A : tTriangularGL k n) = 1 := by simp
  have hentry := congrArg (fun Z : tTriangularGL k n => Z.1.1 i i) hsub
  have hprod : ((A⁻¹ : tTriangularGL k n).1.1 * A.1.1) i i = 1 := by
    calc
      ((A⁻¹ : tTriangularGL k n).1.1 * A.1.1) i i =
          (A⁻¹ * A : tTriangularGL k n).1.1 i i := rfl
      _ = (1 : tTriangularGL k n).1.1 i i := hentry
      _ = 1 := by simp
  rw [tTriangular_mul_apply_diag n (A⁻¹).2 A.2 i] at hprod
  exact eq_inv_of_mul_eq_one_left hprod

public noncomputable def tInvPolynomial (n : ℕ) : (tVariety k n).Coordinates →
    MvPolynomial (tVariety k n).Coordinates k :=
  fun p => match p with
  | Sum.inl q =>
      (∏ i : Fin n, MvPolynomial.X (Sum.inr (ULift.up i))) *
        (Matrix.adjugate (tEntryMatrix n)) q.down.1 q.down.2
  | Sum.inr q =>
      MvPolynomial.X (Sum.inl (ULift.up (q.down, q.down)))

public noncomputable def tMulPolynomial (n : ℕ) : (tVariety k n).Coordinates →
    MvPolynomial ((tVariety k n).Coordinates ⊕ (tVariety k n).Coordinates) k :=
  fun p => match p with
  | Sum.inl q =>
      ∑ l : Fin n,
        MvPolynomial.X (Sum.inl (Sum.inl (ULift.up (q.down.1, l)))) *
          MvPolynomial.X (Sum.inr (Sum.inl (ULift.up (l, q.down.2))))
  | Sum.inr q =>
      MvPolynomial.X (Sum.inl (Sum.inr (ULift.up q.down))) *
        MvPolynomial.X (Sum.inr (Sum.inr (ULift.up q.down)))

/-- The upper-triangular affine variety `T_n` is an algebraic group. -/
public noncomputable instance tAlgebraicGroup
    (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    AlgebraicGroup (tVariety k n) := by
  let e := tPointEquiv k n
  let hGroup : Group (Variety.Point (tVariety k n)) := e.group
  letI : Group (Variety.Point (tVariety k n)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := tMulPolynomial n
      invPolynomial := tInvPolynomial n
      mul_regular := by
        intro p x y
        cases p with
        | inl q =>
            rcases q with ⟨⟨i, j⟩⟩
            change (x * y).val (Sum.inl (ULift.up (i, j))) =
              evalPolynomial (Sum.elim x.val y.val)
                (tMulPolynomial n (Sum.inl (ULift.up (i, j))))
            simp [tMulPolynomial, evalPolynomial]
            change (e.symm (e x * e y)).val (Sum.inl (ULift.up (i, j))) =
              ∑ l : Fin n,
                x.val (Sum.inl (ULift.up (i, l))) *
                  y.val (Sum.inl (ULift.up (l, j)))
            have hz : ∀ z : tTriangularGL k n,
                (e.symm z).val (Sum.inl (ULift.up (i, j))) = z.1.1 i j := by
              intro z
              rfl
            rw [hz]
            rfl
        | inr q =>
            rcases q with ⟨i⟩
            change (x * y).val (Sum.inr (ULift.up i)) =
              evalPolynomial (Sum.elim x.val y.val)
                (tMulPolynomial n (Sum.inr (ULift.up i)))
            simp [tMulPolynomial, evalPolynomial]
            change (e.symm (e x * e y)).val (Sum.inr (ULift.up i)) =
              x.val (Sum.inr (ULift.up i)) * y.val (Sum.inr (ULift.up i))
            have hz : ∀ z : tTriangularGL k n,
                (e.symm z).val (Sum.inr (ULift.up i)) = (z.1.1 i i)⁻¹ := by
              intro z
              rfl
            rw [hz]
            rw [show (e x * e y).1.1 = (e x).1.1 * (e y).1.1 by rfl]
            rw [tTriangular_mul_apply_diag n (e x).2 (e y).2 i]
            have hx : ((e x).1.1 i i)⁻¹ = x.val (Sum.inr (ULift.up i)) := by
              change (tPointMatrix n x i i)⁻¹ = tPointD n x i
              exact (eq_inv_of_mul_eq_one_right
                (tPoint_diag_mul_inv n x i)).symm
            have hy : ((e y).1.1 i i)⁻¹ = y.val (Sum.inr (ULift.up i)) := by
              change (tPointMatrix n y i i)⁻¹ = tPointD n y i
              exact (eq_inv_of_mul_eq_one_right
                (tPoint_diag_mul_inv n y i)).symm
            rw [mul_inv, hx, hy]
      inv_regular := by
        intro p x
        cases p with
        | inl q =>
            rcases q with ⟨⟨i, j⟩⟩
            change x⁻¹.val (Sum.inl (ULift.up (i, j))) =
              evalPolynomial x.val
                (tInvPolynomial n (Sum.inl (ULift.up (i, j))))
            rw [tInvPolynomial, evalPolynomial_mul,
              evalPolynomial_tAdjugate]
            have hEvalProd :
                evalPolynomial x.val
                    (∏ l : Fin n, MvPolynomial.X (Sum.inr (ULift.up l))) =
                  ∏ l : Fin n, tPointD n x l := by
              simp [evalPolynomial, tPointD]
            rw [hEvalProd]
            change (e.symm (e x)⁻¹).val (Sum.inl (ULift.up (i, j))) =
              (∏ l : Fin n, tPointD n x l) *
                Matrix.adjugate (tPointMatrix n x) i j
            have hz : ∀ z : tTriangularGL k n,
                (e.symm z).val (Sum.inl (ULift.up (i, j))) = z.1.1 i j := by
              intro z
              rfl
            rw [hz]
            have hmat : ((e x)⁻¹ : tTriangularGL k n).1.1 =
                (tPointMatrix n x)⁻¹ := by
              simp [Matrix.GeneralLinearGroup]
              rfl
            rw [hmat]
            let hunit : IsUnit (tPointMatrix n x).det :=
              tPoint_det_isUnit n x
            rw [Matrix.nonsing_inv_apply (tPointMatrix n x) hunit]
            simp only [Matrix.smul_apply, smul_eq_mul]
            have hdetProd :
                (tPointMatrix n x).det * (∏ l : Fin n, tPointD n x l) = 1 := by
              rw [det_eq_prod_diagonal_of_tTriangular n
                (tPoint_triangular n x)]
              rw [← Finset.prod_mul_distrib]
              exact Finset.prod_eq_one (fun l _ =>
                tPoint_diag_mul_inv n x l)
            have hcoef : (↑hunit.unit⁻¹ : k) =
                ∏ l : Fin n, tPointD n x l := by
              apply Units.inv_eq_of_mul_eq_one_right
              simpa [hunit.unit_spec] using hdetProd
            rw [hcoef]
        | inr q =>
            rcases q with ⟨i⟩
            change x⁻¹.val (Sum.inr (ULift.up i)) =
              evalPolynomial x.val
                (tInvPolynomial n (Sum.inr (ULift.up i)))
            simp [tInvPolynomial, evalPolynomial]
            change (e.symm (e x)⁻¹).val (Sum.inr (ULift.up i)) =
              x.val (Sum.inl (ULift.up (i, i)))
            have hz : ∀ z : tTriangularGL k n,
                (e.symm z).val (Sum.inr (ULift.up i)) = (z.1.1 i i)⁻¹ := by
              intro z
              rfl
            rw [hz, tTriangularGL_inv_diag, inv_inv]
            rfl }

/-- `tPointEquiv` sends transported multiplication to matrix multiplication. -/
public lemma tPointEquiv_mul (n : ℕ)
    (x y : Variety.Point (tVariety k n)) :
    tPointEquiv k n (x * y) = tPointEquiv k n x * tPointEquiv k n y := by
  have h : x * y = (tPointEquiv k n).symm
      (tPointEquiv k n x * tPointEquiv k n y) := by rfl
  rw [h, Equiv.apply_symm_apply]

/-- `tPointEquiv` sends transported identity to matrix identity. -/
public lemma tPointEquiv_one (n : ℕ) :
    tPointEquiv k n (1 : Variety.Point (tVariety k n)) = 1 := by
  have h : (1 : Variety.Point (tVariety k n)) =
      (tPointEquiv k n).symm 1 := by rfl
  rw [h, Equiv.apply_symm_apply]

/-- The matrix-entry coordinate of a triangular point reconstructed from a
matrix. -/
public lemma tPointEquiv_symm_val_inl (n : ℕ) (A : tTriangularGL k n)
    (q : ULift.{u} (Fin n × Fin n)) :
    ((tPointEquiv k n).symm A).val (Sum.inl q) =
      A.1.1 q.down.1 q.down.2 := rfl

/-- The inverse-diagonal coordinate of a triangular point reconstructed from
a matrix. -/
public lemma tPointEquiv_symm_val_inr (n : ℕ) (A : tTriangularGL k n)
    (q : ULift.{u} (Fin n)) :
    ((tPointEquiv k n).symm A).val (Sum.inr q) =
      (A.1.1 q.down q.down)⁻¹ := rfl

public noncomputable def tDiagonalHom (n : ℕ) :
    tTriangularGL k n →* (Fin n → kˣ) where
  toFun := fun A i => (tDiagIsUnit n A i).unit
  map_one' := by
    ext i
    change ↑(tDiagIsUnit n (1 : tTriangularGL k n) i).unit = (1 : k)
    rw [(tDiagIsUnit n (1 : tTriangularGL k n) i).unit_spec]
    simp
  map_mul' := by
    intro A B
    ext i
    simp only [Pi.mul_apply, Units.val_mul]
    rw [(tDiagIsUnit n (A * B) i).unit_spec,
      (tDiagIsUnit n A i).unit_spec, (tDiagIsUnit n B i).unit_spec]
    rw [show (A * B).1.1 = A.1.1 * B.1.1 by rfl]
    exact tTriangular_mul_apply_diag n A.2 B.2 i

/-- The diagonal homomorphism records the diagonal matrix entries. -/
public lemma tDiagonalHom_val (n : ℕ)
    (x : Variety.Point (tVariety k n)) (i : Fin n) :
    (↑(tDiagonalHom n (tPointEquiv k n x) i) : k) =
      tPointMatrix n x i i := by
  rw [show tDiagonalHom n (tPointEquiv k n x) i =
      (tDiagIsUnit n (tPointEquiv k n x) i).unit by rfl]
  rw [(tDiagIsUnit n (tPointEquiv k n x) i).unit_spec]
  rfl

/-- The inverse of a diagonal unit is the corresponding inverse coordinate. -/
public lemma tDiagonalHom_inv (n : ℕ)
    (x : Variety.Point (tVariety k n)) (i : Fin n) :
    (tDiagonalHom n (tPointEquiv k n x) i).inv = tPointD n x i := by
  exact Units.inv_eq_of_mul_eq_one_right
    (u := tDiagonalHom n (tPointEquiv k n x) i)
    (a := tPointD n x i)
    (by rw [tDiagonalHom_val]; exact tPoint_diag_mul_inv n x i)

/-- The regular diagonal projection from the upper-triangular algebraic group
`T_n` to the diagonal torus `D_n`. -/
@[expose]
public noncomputable def tDiagonalMorphism (n : ℕ) :
    AlgebraicGroup.Morphism (tVariety k n) (dVariety k n) where
  toVariety :=
    { toFun := fun x =>
        (dPointEquiv n).symm (tDiagonalHom n (tPointEquiv k n x))
      regular := by
        intro p
        cases p with
        | inl q =>
            exact ⟨MvPolynomial.X
              (Sum.inl (ULift.up (q.down, q.down))), fun x => by
                change (↑(tDiagonalHom n (tPointEquiv k n x) q.down) : k) = _
                rw [tDiagonalHom_val]
                simp [evalPolynomial, tPointMatrix]⟩
        | inr q =>
            exact ⟨MvPolynomial.X (Sum.inr (ULift.up q.down)), fun x => by
              change (tDiagonalHom n (tPointEquiv k n x) q.down).inv = _
              rw [tDiagonalHom_inv]
              simp [evalPolynomial, tPointD]⟩ }
  map_one := by
    apply (dPointEquiv n).injective
    change tDiagonalHom n (tPointEquiv k n 1) = dPointEquiv n 1
    change tDiagonalHom n 1 = 1
    exact map_one (tDiagonalHom n)
  map_mul := by
    intro x y
    apply (dPointEquiv n).injective
    change tDiagonalHom n (tPointEquiv k n (x * y)) =
      dPointEquiv n
        ((dPointEquiv n).symm (tDiagonalHom n (tPointEquiv k n x)) *
          (dPointEquiv n).symm (tDiagonalHom n (tPointEquiv k n y)))
    change tDiagonalHom n (tPointEquiv k n x * tPointEquiv k n y) =
      tDiagonalHom n (tPointEquiv k n x) *
        tDiagonalHom n (tPointEquiv k n y)
    exact map_mul (tDiagonalHom n) _ _

private lemma tDiagonalMorphism_point (n : ℕ)
    (x : Variety.Point (tVariety k n)) :
    dPointEquiv n ((tDiagonalMorphism n).onPoints x) =
      tDiagonalHom n (tPointEquiv k n x) := by
  change dPointEquiv n ((dPointEquiv n).symm
    (tDiagonalHom n (tPointEquiv k n x))) = _
  exact Equiv.apply_symm_apply _ _

/-- A triangular point lies in the diagonal kernel exactly when all of its
diagonal entries equal one. -/
public lemma tDiagonalMorphism_mem_kernel_iff (n : ℕ)
    (x : Variety.Point (tVariety k n)) :
    x ∈ (tDiagonalMorphism n).kernel ↔
      ∀ i : Fin n, tPointMatrix n x i i = 1 := by
  change (tDiagonalMorphism n).onPoints x = 1 ↔ _
  constructor
  · intro hx i
    have h := congrArg (dPointEquiv n) hx
    have hone : dPointEquiv n (1 : Variety.Point (dVariety k n)) = 1 := rfl
    rw [tDiagonalMorphism_point, hone] at h
    have hi := congrFun h i
    have hval := congrArg (fun z : kˣ => (z : k)) hi
    change (↑(tDiagonalHom n (tPointEquiv k n x) i) : k) = 1 at hval
    rw [tDiagonalHom_val] at hval
    exact hval
  · intro hx
    apply (dPointEquiv n).injective
    have hone : dPointEquiv n (1 : Variety.Point (dVariety k n)) = 1 := rfl
    rw [tDiagonalMorphism_point, hone]
    ext i
    change (↑(tDiagonalHom n (tPointEquiv k n x) i) : k) = 1
    rw [tDiagonalHom_val, hx i]

/-- The closed normal kernel of the diagonal projection `T_n → D_n`. -/
@[expose]
public noncomputable def tUnipotentKernel (n : ℕ) : ClosedSubgroup (tVariety k n) :=
  (tDiagonalMorphism n).kernelClosedSubgroup

/-- The algebraic-group structure on the carrier variety of the unipotent
kernel of `T_n → D_n`. -/
public noncomputable instance tUnipotentKernelAlgebraicGroup (n : ℕ) :
    AlgebraicGroup (tUnipotentKernel (k := k) n).carrierVariety :=
  ClosedSubgroup.carrierAlgebraicGroup (tUnipotentKernel (k := k) n)

end

end Theory.AlgebraicGroup

