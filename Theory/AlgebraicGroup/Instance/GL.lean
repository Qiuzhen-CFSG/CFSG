module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Theory.AlgebraicGroup.Basic

universe u v

/-!
Examples 1.1.7: the general linear group `GLₙ` as an affine zero locus.

The zero-locus presentation adds to the `n²` matrix entries a coordinate `t`
for the inverse of the determinant; the single equation `det A · t - 1 = 0`
cuts out exactly the invertible matrices (`glPointEquiv`).  The group law of
`GLₙ` is polynomial: multiplication is matrix multiplication, and inversion is
`t · adj(A)` by Cramer's rule, so the zero locus is an algebraic group
(`glAlgebraicGroup`).  The four subgroups `SLₙ`, `Tₙ`, `Dₙ`, `Uₙ` of Examples
1.1.7 can each be realized as a closed subgroup of this zero-locus (see the
trailing note); every closed subgroup of `GLₙ` carries the algebraic-group
structure of the ambient by the `ClosedSubgroup.carrierAlgebraicGroup`
mechanism, which is the anchoring of Definition 1.1.1 (algebraic groups as
closed subgroups of some `GLₙ`).
-/

namespace Theory.AlgebraicGroup

section

open scoped TensorProduct BigOperators

open LinearMap Submodule

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ## The zero-locus presentation of `GLₙ` -/

/-- The determinant of the generic matrix as a polynomial in the entries. -/
public noncomputable abbrev glDetPolynomial (n : ℕ) : MvPolynomial (Fin n × Fin n) k :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) k)

/-- The adjugate of the generic matrix as a matrix of entry polynomials. -/
public noncomputable abbrev glAdjugateMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  Matrix.adjugate (Matrix.mvPolynomialX (Fin n) (Fin n) k)

/-- The single defining equation of `GLₙ`: `det A · t - 1 = 0`. -/
public noncomputable def glEquations (n : ℕ) : Set (MvPolynomial ((Fin n × Fin n) ⊕ PUnit) k) :=
  {MvPolynomial.rename Sum.inl (glDetPolynomial n) * MvPolynomial.X (Sum.inr PUnit.unit) - 1}

/-- The coordinate type of the `GLₙ` zero locus: the `n²` matrix entries plus
a scalar coordinate for the inverse determinant. -/
public abbrev glCoordinates (n : ℕ) : Type u := (Fin n × Fin n) ⊕ PUnit

/-- The general linear group `GLₙ` as an affine zero locus (Examples 1.1.7):
the points are pairs `(A, t)` of an `n × n` matrix and a scalar satisfying
`det A · t = 1`. -/
public noncomputable abbrev glVariety (n : ℕ) : Variety k where
  Coordinates := glCoordinates n
  finiteCoordinates := inferInstance
  equations := glEquations n

/-- The matrix part of a `GLₙ` point. -/
@[expose]
public def glMatrixOfPoint (n : ℕ) (x : Variety.Point (glVariety n : Variety k)) :
    Matrix (Fin n) (Fin n) k :=
  fun i j => x.val (Sum.inl (i, j))

/-- The determinant-coordinate part of a `GLₙ` point. -/
@[expose]
public def glScalarOfPoint (n : ℕ) (x : Variety.Point (glVariety n : Variety k)) : k :=
  x.val (Sum.inr PUnit.unit)

omit [IsAlgClosed k] in
/-- The determinant of the matrix part of a point is the scalar part evaluated
by the zero-locus equation: `det A · t = 1`. -/
public lemma glPoint_det_mul_scalar (n : ℕ) (x : Variety.Point (glVariety n : Variety k)) :
    (glMatrixOfPoint n x).det * glScalarOfPoint n x = 1 := by
  have hz := x.isZero (MvPolynomial.rename Sum.inl (glDetPolynomial n) *
    MvPolynomial.X (Sum.inr PUnit.unit) - 1) (by
      simp [glEquations])
  have hdet : evalPolynomial x.val (MvPolynomial.rename Sum.inl (glDetPolynomial n)) =
      (glMatrixOfPoint n x).det := by
    rw [evalPolynomial_rename]
    rw [evalPolynomial]
    rw [glDetPolynomial]
    change MvPolynomial.eval (x.val ∘ Sum.inl)
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) k)) = (glMatrixOfPoint n x).det
    rw [Matrix.eval_det_mvPolynomialX]
    rfl
  have ht : evalPolynomial x.val (MvPolynomial.X (Sum.inr PUnit.unit)) = glScalarOfPoint n x := by
    simp [glScalarOfPoint, evalPolynomial]
  have hEq : (glMatrixOfPoint n x).det * glScalarOfPoint n x - 1 = 0 := by
    have hz' : evalPolynomial x.val (MvPolynomial.rename Sum.inl (glDetPolynomial n) *
        MvPolynomial.X (Sum.inr PUnit.unit) - 1) = 0 := hz
    have hExp : evalPolynomial x.val (MvPolynomial.rename Sum.inl (glDetPolynomial n)) *
          evalPolynomial x.val (MvPolynomial.X (Sum.inr PUnit.unit)) - 1 = 0 := by
      simpa [evalPolynomial] using hz'
    rw [hdet, ht] at hExp
    exact hExp
  exact sub_eq_zero.mp hEq

omit [IsAlgClosed k] in
/-- The scalar coordinate of a point is the inverse of the determinant. -/
public lemma glScalarOfPoint_eq_inv_det (n : ℕ) (x : Variety.Point (glVariety n : Variety k)) :
    glScalarOfPoint n x = (glMatrixOfPoint n x).det⁻¹ := by
  have h : (glMatrixOfPoint n x).det * glScalarOfPoint n x = 1 := glPoint_det_mul_scalar n x
  have hdet0 : (glMatrixOfPoint n x).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  calc
    glScalarOfPoint n x = (glMatrixOfPoint n x).det⁻¹ *
        ((glMatrixOfPoint n x).det * glScalarOfPoint n x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hdet0, one_mul]
    _ = (glMatrixOfPoint n x).det⁻¹ := by rw [h, mul_one]

/-- The rational points of the zero locus are exactly the invertible matrices:
`Point (glVariety n) ≃ GLₙ(k)`. -/
@[expose]
public noncomputable def glPointEquiv (n : ℕ) : Variety.Point (glVariety n : Variety k) ≃ GL (Fin n) k where
  toFun := fun x ↦
    let A : Matrix (Fin n) (Fin n) k := glMatrixOfPoint n x
    let hIsUnit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (by
      apply isUnit_iff_ne_zero.mpr
      intro h0
      have hdet1 : (glMatrixOfPoint n x).det * glScalarOfPoint n x = 1 :=
        glPoint_det_mul_scalar n x
      have : (0 : k) = 1 := by
        calc
          (0 : k) = (glMatrixOfPoint n x).det * glScalarOfPoint n x := by rw [h0, zero_mul]
          _ = 1 := hdet1
      exact zero_ne_one this)
    hIsUnit.unit
  invFun := fun A ↦
    let M : Matrix (Fin n) (Fin n) k := (A : Matrix (Fin n) (Fin n) k)
    have hdet0 : M.det ≠ 0 := by
      intro h
      have hunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det (A := M)).mp A.isUnit
      exact hunit.ne_zero h
    ⟨Sum.elim (fun p : Fin n × Fin n => M p.1 p.2) (fun _ => M.det⁻¹), by
      intro p hp
      have hp' : p = MvPolynomial.rename Sum.inl (glDetPolynomial n) *
          MvPolynomial.X (Sum.inr PUnit.unit) - 1 := by
        simpa [glEquations] using hp
      rw [hp']
      have hE : MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2) (glDetPolynomial n) = M.det := by
        rw [glDetPolynomial]
        rw [Matrix.eval_det_mvPolynomialX]
        rfl
      have hEq : M.det * M.det⁻¹ - 1 = 0 := by
        rw [mul_inv_cancel₀ hdet0, sub_self]
      simpa [evalPolynomial, MvPolynomial.eval_rename, hE] using hEq⟩
  left_inv := by
    intro x
    apply Variety.Point.ext
    funext c
    cases c with
    | inl p =>
        rcases p with ⟨i, j⟩
        rfl
    | inr PUnit.unit =>
        -- t = det⁻¹
        change (glMatrixOfPoint n x).det⁻¹ = glScalarOfPoint n x
        exact (glScalarOfPoint_eq_inv_det n x).symm
  right_inv := by
    intro A
    apply Units.ext
    rfl

/-! ## The polynomial group law of `GLₙ` -/

/-- The group law of `GLₙ` is polynomial: matrix multiplication for the
entries, multiplication of the determinant coordinates for `t`. -/
@[expose]
public noncomputable def glMulPolynomial (n : ℕ) : (Fin n × Fin n) ⊕ PUnit →
    MvPolynomial (((Fin n × Fin n) ⊕ PUnit) ⊕ ((Fin n × Fin n) ⊕ PUnit)) k :=
  fun
    | Sum.inl (i, j) => ∑ c : Fin n,
        MvPolynomial.X (Sum.inl (Sum.inl (i, c))) * MvPolynomial.X (Sum.inr (Sum.inl (c, j)))
    | Sum.inr PUnit.unit => MvPolynomial.X (Sum.inl (Sum.inr PUnit.unit)) *
        MvPolynomial.X (Sum.inr (Sum.inr PUnit.unit))

/-- The inversion law of `GLₙ` is polynomial: `A⁻¹ = t · adj(A)` by Cramer's
rule, and the determinant coordinate of the inverse is `det A`. -/
@[expose]
public noncomputable def glInvPolynomial (n : ℕ) : (Fin n × Fin n) ⊕ PUnit →
    MvPolynomial ((Fin n × Fin n) ⊕ PUnit) k :=
  fun
    | Sum.inl (i, j) => MvPolynomial.X (Sum.inr PUnit.unit) *
        MvPolynomial.rename Sum.inl (glAdjugateMatrix n i j)
    | Sum.inr PUnit.unit => MvPolynomial.rename Sum.inl (glDetPolynomial n)

end

section

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The algebraic group `GL(V)` for a finite-dimensional vector space, obtained
by transporting the `GLₙ` structure along a basis.  The construction is
basis-independent: different bases give different point equivalences, but
the transported multiplication and inverse polynomials agree. -/
@[expose]
public noncomputable def glVarietyOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] : Variety k :=
  (glVariety (Module.finrank k V) : Variety k)

/-- Point equivalence `Point (glVarietyOf V) ≃ GL(V)` induced by a basis. -/
@[expose]
public noncomputable def glPointEquivOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    Variety.Point (glVarietyOf k V) ≃ LinearMap.GeneralLinearGroup k V := by
  let eGL : GL (Fin (Module.finrank k V)) k ≃
      LinearMap.GeneralLinearGroup k (Fin (Module.finrank k V) → k) :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin (Module.finrank k V)) (R := k)).toEquiv
  let eLin : LinearMap.GeneralLinearGroup k (Fin (Module.finrank k V) → k) ≃
      LinearMap.GeneralLinearGroup k V :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm).toEquiv
  exact (glPointEquiv (Module.finrank k V)).trans (eGL.trans eLin)

/-- Matrix of a `GL(V)` point in the chosen basis. -/
public noncomputable def glPointMatrixOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (glVarietyOf k V)) :
    Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k :=
  fun i j => e.repr (((glPointEquivOf k V e) x).1 (e j)) i

/-- The action of a basis-transported point on a basis vector is the inverse
coordinate map applied to the corresponding matrix column. -/
public lemma glPointEquivOf_apply_basis (V : Type v) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (glVarietyOf k V)) (j : Fin (Module.finrank k V)) :
    (glPointEquivOf k V e x).1 (e j) =
      e.equivFun.symm
        (fun l : Fin (Module.finrank k V) => glMatrixOfPoint (Module.finrank k V) x l j) := by
  dsimp [glPointEquivOf]
  change e.equivFun.symm
      (((glPointEquiv (Module.finrank k V) x).1).mulVec (e.equivFun (e j))) =
      e.equivFun.symm (fun l => glMatrixOfPoint (Module.finrank k V) x l j)
  have hsingle : e.equivFun (e j) = Pi.single j (1 : k) := by
    funext l
    rw [Module.Basis.equivFun_apply, Module.Basis.repr_self_apply]
    by_cases hjl : j = l
    · simp [hjl]
    · simp [hjl, Ne.symm hjl]
  have hcol : ((glPointEquiv (Module.finrank k V) x).1).mulVec (Pi.single j (1 : k)) =
      fun l => glMatrixOfPoint (Module.finrank k V) x l j := by
    funext l
    simp [glPointEquiv, glMatrixOfPoint, Matrix.mulVec_single]
  rw [hsingle, hcol]

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The transported group structure on the rational points of `GLₙ`. -/
public noncomputable instance glPointGroup (n : ℕ) : Group (Variety.Point (glVariety n : Variety k)) :=
  (glPointEquiv (n := n)).group

public noncomputable instance glAlgebraicGroup (n : ℕ) : AlgebraicGroup (glVariety n : Variety k) where
  toGroup := (glPointEquiv (n := n)).group
  mulPolynomial := glMulPolynomial n
  invPolynomial := glInvPolynomial n
  mul_regular := by
    intro idx x y
    let e : Variety.Point (glVariety n : Variety k) ≃ GL (Fin n) k := glPointEquiv (n := n)
    let A := e x
    let B := e y
    have hx : x = e.symm A := (e.symm_apply_apply x).symm
    have hy : y = e.symm B := (e.symm_apply_apply y).symm
    rw [hx, hy]
    rcases idx with ⟨i, j⟩ | ⟨⟩
    · simp only [glMulPolynomial]
      change (e.symm (A * B)).val (Sum.inl (i, j)) =
        evalPolynomial (Sum.elim (e.symm A).val (e.symm B).val)
          (∑ c : Fin n,
            MvPolynomial.X (Sum.inl (Sum.inl (i, c))) * MvPolynomial.X (Sum.inr (Sum.inl (c, j))))
      rw [show (e.symm (A * B)).val (Sum.inl (i, j)) = (A * B : Matrix (Fin n) (Fin n) k) i j by
        change (A * B : Matrix (Fin n) (Fin n) k) i j = (A * B : Matrix (Fin n) (Fin n) k) i j
        rfl]
      rw [Matrix.mul_apply]
      have hEv : evalPolynomial (Sum.elim (e.symm A).val (e.symm B).val)
            (∑ c : Fin n,
              MvPolynomial.X (Sum.inl (Sum.inl (i, c))) * MvPolynomial.X (Sum.inr (Sum.inl (c, j)))) =
          ∑ c : Fin n, (A : Matrix (Fin n) (Fin n) k) i c * (B : Matrix (Fin n) (Fin n) k) c j := by
        simp [evalPolynomial_sum, evalPolynomial_mul, evalPolynomial_X]
        apply Finset.sum_congr rfl
        intro c hc
        have hAentry : (e.symm A).val (Sum.inl (i, c)) = (A : Matrix (Fin n) (Fin n) k) i c := by
          change (A : Matrix (Fin n) (Fin n) k) i c = (A : Matrix (Fin n) (Fin n) k) i c
          rfl
        have hBentry : (e.symm B).val (Sum.inl (c, j)) = (B : Matrix (Fin n) (Fin n) k) c j := by
          change (B : Matrix (Fin n) (Fin n) k) c j = (B : Matrix (Fin n) (Fin n) k) c j
          rfl
        rw [hAentry, hBentry]
      rw [hEv]
    · simp only [glMulPolynomial]
      change (e.symm (A * B)).val (Sum.inr PUnit.unit) =
        evalPolynomial (Sum.elim (e.symm A).val (e.symm B).val)
          (MvPolynomial.X (Sum.inl (Sum.inr PUnit.unit)) * MvPolynomial.X (Sum.inr (Sum.inr PUnit.unit)))
      -- the determinant coordinate of AB is t_A · t_B
      rw [show (e.symm (A * B)).val (Sum.inr PUnit.unit) =
          ((A * B : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det⁻¹ by
        change ((A * B : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det⁻¹ =
          ((A * B : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det⁻¹
        rfl]
      have hEv : evalPolynomial (Sum.elim (e.symm A).val (e.symm B).val)
            (MvPolynomial.X (Sum.inl (Sum.inr PUnit.unit)) * MvPolynomial.X (Sum.inr (Sum.inr PUnit.unit))) =
          glScalarOfPoint n (e.symm A) * glScalarOfPoint n (e.symm B) := by
        simp [evalPolynomial_mul, evalPolynomial_X, glScalarOfPoint]
      rw [hEv]
      -- (A·B).det⁻¹ = A.det⁻¹ · B.det⁻¹
      change ((A : Matrix (Fin n) (Fin n) k) * (B : Matrix (Fin n) (Fin n) k)).det⁻¹ =
          glScalarOfPoint n (e.symm A) * glScalarOfPoint n (e.symm B)
      rw [Matrix.det_mul]
      rw [mul_inv, mul_comm]
      rw [glScalarOfPoint_eq_inv_det (n := n) (x := e.symm A),
        glScalarOfPoint_eq_inv_det (n := n) (x := e.symm B)]
      have hA : (glMatrixOfPoint n (e.symm A)).det = (A : Matrix (Fin n) (Fin n) k).det := by
        congr 1
      have hB : (glMatrixOfPoint n (e.symm B)).det = (B : Matrix (Fin n) (Fin n) k).det := by
        congr 1
      rw [hA, hB]
      ring
  inv_regular := by
    intro idx x
    let e : Variety.Point (glVariety n : Variety k) ≃ GL (Fin n) k := glPointEquiv (n := n)
    let A := e x
    have hx : x = e.symm A := (e.symm_apply_apply x).symm
    rw [hx]
    rcases idx with ⟨i, j⟩ | ⟨⟩
    · simp only [glInvPolynomial]
      change (e.symm A⁻¹).val (Sum.inl (i, j)) =
        evalPolynomial (e.symm A).val
          (MvPolynomial.X (Sum.inr PUnit.unit) *
            MvPolynomial.rename Sum.inl (glAdjugateMatrix n i j))
      -- (A⁻¹)(i,j) = t · adj(A)(i,j)
      have hunit : IsUnit ((A : Matrix (Fin n) (Fin n) k).det) :=
        (Matrix.isUnit_iff_isUnit_det (A := (A : Matrix (Fin n) (Fin n) k))).mp A.isUnit
      have hinv : (A : Matrix (Fin n) (Fin n) k)⁻¹ =
          ((↑hunit.unit⁻¹ : k) • (A : Matrix (Fin n) (Fin n) k).adjugate) :=
        Matrix.nonsing_inv_apply (A := (A : Matrix (Fin n) (Fin n) k)) hunit
      rw [show (e.symm A⁻¹).val (Sum.inl (i, j)) = (A : Matrix (Fin n) (Fin n) k)⁻¹ i j by
        change ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = (A : Matrix (Fin n) (Fin n) k)⁻¹ i j
        -- (↑(A⁻¹) : Matrix) = (↑A : Matrix)⁻¹, entry-wise
        have h : ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
            (A : Matrix (Fin n) (Fin n) k) = 1 := Units.inv_mul A
        have hcoec : ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
            (A : Matrix (Fin n) (Fin n) k)⁻¹ := (Matrix.inv_eq_left_inv h).symm
        rw [hcoec]]
      -- adjugate commutes with evaluation
      have hadj : MvPolynomial.eval₂ (RingHom.id k)
          (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2)
            (glAdjugateMatrix n i j) =
          (A : Matrix (Fin n) (Fin n) k).adjugate i j := by
        rw [glAdjugateMatrix]
        have hma : (RingHom.mapMatrix (MvPolynomial.eval₂Hom (RingHom.id k)
              (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2))
              (Matrix.adjugate (Matrix.mvPolynomialX (Fin n) (Fin n) k))) i j =
            (Matrix.adjugate (RingHom.mapMatrix (MvPolynomial.eval₂Hom (RingHom.id k)
              (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2))
                (Matrix.mvPolynomialX (Fin n) (Fin n) k))) i j := by
          exact congr_fun (congr_fun (RingHom.map_adjugate (MvPolynomial.eval₂Hom (RingHom.id k)
            (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2))
            (Matrix.mvPolynomialX (Fin n) (Fin n) k)) i) j
        calc
          MvPolynomial.eval₂ (RingHom.id k)
              (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2)
              (Matrix.adjugate (Matrix.mvPolynomialX (Fin n) (Fin n) k) i j) =
              (RingHom.mapMatrix (MvPolynomial.eval₂Hom (RingHom.id k)
                (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2))
                (Matrix.adjugate (Matrix.mvPolynomialX (Fin n) (Fin n) k))) i j := by
                rfl
          _ = (Matrix.adjugate (RingHom.mapMatrix (MvPolynomial.eval₂Hom (RingHom.id k)
                (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2))
                  (Matrix.mvPolynomialX (Fin n) (Fin n) k))) i j := by
                rw [hma]
          _ = (A : Matrix (Fin n) (Fin n) k).adjugate i j := by
                have hmap : RingHom.mapMatrix (MvPolynomial.eval₂Hom (RingHom.id k)
                      (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2))
                    (Matrix.mvPolynomialX (Fin n) (Fin n) k) = (A : Matrix (Fin n) (Fin n) k) := by
                  exact Matrix.mvPolynomialX_map_eval₂ _ (A : Matrix (Fin n) (Fin n) k)
                rw [hmap]
      -- t = det⁻¹ = hunit.unit⁻¹
      have ht : (↑hunit.unit⁻¹ : k) = glScalarOfPoint n (e.symm A) := by
        calc
          (↑hunit.unit⁻¹ : k) = ((↑hunit.unit : k)⁻¹) := by
            exact eq_inv_of_mul_eq_one_right (Units.val_inv hunit.unit)
          _ = ((A : Matrix (Fin n) (Fin n) k).det)⁻¹ := by
            rw [hunit.unit_spec]
          _ = glScalarOfPoint n (e.symm A) := by
            rw [glScalarOfPoint_eq_inv_det]
            congr 1
      rw [hinv]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [ht]
      rw [evalPolynomial_mul, evalPolynomial_X]
      rw [show (e.symm A).val (Sum.inr PUnit.unit) = glScalarOfPoint n (e.symm A) by rfl]
      have hAdjE : evalPolynomial (e.symm A).val (MvPolynomial.rename Sum.inl (glAdjugateMatrix n i j)) =
          (A : Matrix (Fin n) (Fin n) k).adjugate i j := by
        rw [evalPolynomial_rename]
        have hfun : (e.symm A).val ∘ Sum.inl =
            (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) k) p.1 p.2) := by
          funext p
          rcases p with ⟨i0, j0⟩
          change (A : Matrix (Fin n) (Fin n) k) i0 j0 = (A : Matrix (Fin n) (Fin n) k) i0 j0
          rfl
        rw [hfun]
        exact hadj
      rw [hAdjE]
    · simp only [glInvPolynomial]
      change (e.symm A⁻¹).val (Sum.inr PUnit.unit) =
        evalPolynomial (e.symm A).val (MvPolynomial.rename Sum.inl (glDetPolynomial n))
      -- the determinant coordinate of A⁻¹ is det A
      rw [show (e.symm A⁻¹).val (Sum.inr PUnit.unit) =
          ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det⁻¹ by
        change ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det⁻¹ =
          ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det⁻¹
        rfl]
      have hR : evalPolynomial (e.symm A).val (MvPolynomial.rename Sum.inl (glDetPolynomial n)) =
          (A : Matrix (Fin n) (Fin n) k).det := by
        rw [evalPolynomial_rename, glDetPolynomial]
        change MvPolynomial.eval ((e.symm A).val ∘ Sum.inl)
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) k)) = (A : Matrix (Fin n) (Fin n) k).det
        rw [Matrix.eval_det_mvPolynomialX]
        congr 1
      rw [hR]
      have hcoec : ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
          (A : Matrix (Fin n) (Fin n) k)⁻¹ := (Matrix.inv_eq_left_inv (Units.inv_mul A)).symm
      rw [hcoec]
      have hdetinv : (A : Matrix (Fin n) (Fin n) k)⁻¹.det =
          ((A : Matrix (Fin n) (Fin n) k).det)⁻¹ := by
        have h1 : (A : Matrix (Fin n) (Fin n) k)⁻¹.det * (A : Matrix (Fin n) (Fin n) k).det = 1 := by
          calc
            (A : Matrix (Fin n) (Fin n) k)⁻¹.det * (A : Matrix (Fin n) (Fin n) k).det
                = ((A : Matrix (Fin n) (Fin n) k)⁻¹ * (A : Matrix (Fin n) (Fin n) k)).det := by
                  rw [Matrix.det_mul]
            _ = 1 := by
                  have hcoec' : ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
                      (A : Matrix (Fin n) (Fin n) k)⁻¹ := (Matrix.inv_eq_left_inv (Units.inv_mul A)).symm
                  rw [← hcoec']
                  rw [Units.inv_mul, Matrix.det_one]
        rw [eq_inv_of_mul_eq_one_right h1]
        rw [inv_inv]
      rw [hdetinv]
      rw [inv_inv]

end

/-! The multiplicative equivalence between `GLₙ` points and invertible matrices. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def translationGLPointMulEquiv (n : ℕ) :
    Variety.Point (glVariety n : Variety k) ≃* GL (Fin n) k where
  toEquiv := glPointEquiv n
  map_mul' := by
    intro x y
    change (glPointEquiv n)
      ((glPointEquiv n).symm
        ((glPointEquiv n) x * (glPointEquiv n) y)) = _
    rw [Equiv.apply_symm_apply]
    rfl

end

section

public noncomputable instance glAlgebraicGroupOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] :
    AlgebraicGroup (glVarietyOf k V) := by
  change AlgebraicGroup ((glVariety (Module.finrank k V) : Variety k))
  exact glAlgebraicGroup (Module.finrank k V)

end

end Theory.AlgebraicGroup
