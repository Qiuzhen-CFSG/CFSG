module

public import Theory.AlgebraicGroup.Instance.U

universe u

namespace Theory.AlgebraicGroup

/-!
Lower-triangular infrastructure for matrix big-cell constructions.  The
existing `tTriangular` and `uUnipotent` APIs are upper-triangular, so the
lower variants are transported through transpose.  This supplies the
closure, determinant, inverse, and `GL` subgroup facts needed by an LDU
factorization without duplicating the adjugate calculation.
-/

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def lTriangular (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : Prop :=
  tTriangular n (Matrix.transpose A)

@[expose]
public def lUnipotent (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : Prop :=
  lTriangular n A ∧ ∀ i : Fin n, A i i = 1

omit [IsAlgClosed k] in
public lemma lTriangular_mul (n : ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : lTriangular n A) (hB : lTriangular n B) : lTriangular n (A * B) := by
  rw [lTriangular, Matrix.transpose_mul]
  exact tTriangular_mul n hB hA

omit [IsAlgClosed k] in
public lemma lTriangular_det (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : lTriangular n A) : A.det = ∏ i : Fin n, A i i := by
  have h := det_eq_prod_diagonal_of_tTriangular n (A := Matrix.transpose A) hA
  simpa [lTriangular, Matrix.det_transpose, Matrix.transpose_apply] using h

omit [IsAlgClosed k] in
public lemma lTriangular_inv (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : lTriangular n A) (hdet : IsUnit A.det) : lTriangular n A⁻¹ := by
  change tTriangular n (Matrix.transpose (A⁻¹))
  rw [Matrix.transpose_nonsing_inv]
  exact tTriangular_inv n hA (by simpa [Matrix.det_transpose] using hdet)

@[expose]
public def lTriangularGL (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    Subgroup (GL (Fin n) k) where
  carrier := {g : GL (Fin n) k | lTriangular n g.1}
  one_mem' := by
    intro i j hij
    simpa [lTriangular, Matrix.transpose_apply, Matrix.one_apply] using
      (Ne.symm (ne_of_gt hij))
  mul_mem' := by
    intro a b ha hb
    exact lTriangular_mul n ha hb
  inv_mem' := by
    intro a ha
    change lTriangular n ((a⁻¹ : GL (Fin n) k).1)
    have hgl : (a⁻¹ : GL (Fin n) k).1 = a.1⁻¹ := by
      exact (Units.inv_eq_of_mul_eq_one_right (u := a) (a := a.1⁻¹) (by
        exact Matrix.mul_nonsing_inv a.1 (a.isUnit.map Matrix.detMonoidHom)))
    rw [hgl]
    exact lTriangular_inv n ha (a.isUnit.map Matrix.detMonoidHom)

omit [IsAlgClosed k] in
public lemma lUnipotent_mul (n : ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : lUnipotent n A) (hB : lUnipotent n B) : lUnipotent n (A * B) := by
  refine ⟨lTriangular_mul n hA.1 hB.1, ?_⟩
  intro i
  have hdiag := tTriangular_mul_apply_diag n hB.1 hA.1 i
  have hdiag' : (A * B) i i = B i i * A i i := by
    have ht := congrArg (fun M : Matrix (Fin n) (Fin n) k => M i i)
      (Matrix.transpose_mul A B)
    rw [hdiag] at ht
    simpa [Matrix.transpose_apply] using ht
  simpa [hA.2 i, hB.2 i] using hdiag'

omit [IsAlgClosed k] in
public lemma lUnipotent_inv (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : lUnipotent n A) : lUnipotent n A⁻¹ := by
  have hAt : uUnipotent n (Matrix.transpose A) := by
    refine ⟨hA.1, ?_⟩
    intro i
    simpa [Matrix.transpose_apply] using hA.2 i
  change uUnipotent n (Matrix.transpose (A⁻¹))
  rw [Matrix.transpose_nonsing_inv]
  exact uUnipotent_inv n hAt

@[expose]
public def lUnipotentGL (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    Subgroup (GL (Fin n) k) where
  carrier := {g : GL (Fin n) k | lUnipotent n g.1}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      simpa [lTriangular, Matrix.transpose_apply, Matrix.one_apply] using
        (Ne.symm (ne_of_gt hij))
    · intro i
      simp
  mul_mem' := by
    intro a b ha hb
    exact lUnipotent_mul n ha hb
  inv_mem' := by
    intro a ha
    change lUnipotent n ((a⁻¹ : GL (Fin n) k).1)
    have hgl : (a⁻¹ : GL (Fin n) k).1 = a.1⁻¹ := by
      exact (Units.inv_eq_of_mul_eq_one_right (u := a) (a := a.1⁻¹) (by
        exact Matrix.mul_nonsing_inv a.1 (a.isUnit.map Matrix.detMonoidHom)))
    rw [hgl]
    exact lUnipotent_inv n ha

/-! The affine carrier for lower-unitriangular matrices. -/

public abbrev lVariety (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) : Variety k where
  Coordinates := ULift.{u} (Fin n × Fin n)
  finiteCoordinates := inferInstance
  equations : Set (MvPolynomial (ULift.{u} (Fin n × Fin n)) k) :=
    {p | (∃ i j : Fin n, i < j ∧ p = MvPolynomial.X (ULift.up (i, j))) ∨
         (∃ i : Fin n, p = MvPolynomial.X (ULift.up (i, i)) - 1)}

@[expose]
public def lPointMatrix (n : ℕ) (x : Variety.Point (lVariety k n)) :
    Matrix (Fin n) (Fin n) k :=
  fun i j => x.val (ULift.up (i, j))

public lemma lPoint_lUnipotent (n : ℕ) (x : Variety.Point (lVariety k n)) :
    lUnipotent n (lPointMatrix n x) := by
  constructor
  · intro i j hij
    have h := x.isZero (MvPolynomial.X (ULift.up (j, i))) (by
      exact Set.mem_ofPred.mpr (Or.inl ⟨j, i, hij, rfl⟩))
    simpa [lTriangular, lPointMatrix, Matrix.transpose_apply, evalPolynomial] using h
  · intro i
    have h := x.isZero (MvPolynomial.X (ULift.up (i, i)) - 1) (by
      exact Set.mem_ofPred.mpr (Or.inr ⟨i, rfl⟩))
    have hsum : evalPolynomial x.val (MvPolynomial.X (ULift.up (i, i))) - 1 = 0 := by
      simpa [evalPolynomial] using h
    simpa [lPointMatrix, evalPolynomial] using (sub_eq_zero.mp hsum)

public lemma lPoint_det_isUnit (n : ℕ) (x : Variety.Point (lVariety k n)) :
    IsUnit ((lPointMatrix n x).det : k) := by
  rw [lTriangular_det n (lPoint_lUnipotent n x).1]
  have hprod : (∏ i : Fin n, lPointMatrix n x i i) = 1 :=
    Finset.prod_eq_one (fun i hi => (lPoint_lUnipotent n x).2 i)
  rw [hprod]
  exact isUnit_one

@[expose]
public noncomputable def lPointEquiv (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    Variety.Point (lVariety k n) ≃ lUnipotentGL k n := by
  refine ⟨fun x => ⟨Matrix.GeneralLinearGroup.mk'' (lPointMatrix n x)
      (lPoint_det_isUnit n x), ?_⟩, fun A => ⟨?_, ?_⟩, ?_, ?_⟩
  · change lUnipotent n (Matrix.GeneralLinearGroup.mk'' (lPointMatrix n x)
      (lPoint_det_isUnit n x)).1
    rw [show (Matrix.GeneralLinearGroup.mk'' (lPointMatrix n x)
      (lPoint_det_isUnit n x)).1 = lPointMatrix n x by rfl]
    exact lPoint_lUnipotent n x
  · exact fun p : ULift.{u} (Fin n × Fin n) => A.1.1 p.down.1 p.down.2
  · intro p hp
    rcases Set.mem_ofPred.mp hp with h | h
    · rcases h with ⟨i, j, hij, rfl⟩
      simpa [evalPolynomial] using A.2.1 hij
    · rcases h with ⟨i, rfl⟩
      simpa [evalPolynomial] using (sub_eq_zero.mpr (A.2.2 i))
  · intro x
    apply Variety.Point.ext
    funext p
    rfl
  · intro A
    apply Subtype.ext
    apply Units.ext
    ext i j
    rfl

end Theory.AlgebraicGroup
