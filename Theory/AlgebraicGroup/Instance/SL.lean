module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Theory.AlgebraicGroup.Basic

universe u v

namespace Theory.AlgebraicGroup

section
open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Matrix of coordinate variables for `SLₙ`. -/
@[expose]
public noncomputable def slEntryMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (ULift.{u} (Fin n × Fin n)) k) :=
  fun i j => MvPolynomial.X (ULift.up (i, j))

/-- Determinant polynomial for `SLₙ`. -/
public noncomputable def slDetPoly (n : ℕ) : MvPolynomial (ULift.{u} (Fin n × Fin n)) k :=
  (slEntryMatrix n).det

/-- Affine zero locus for `SLₙ`, imposing determinant one. -/
public abbrev slVariety (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) : Variety k where
  Coordinates := ULift.{u} (Fin n × Fin n)
  finiteCoordinates := inferInstance
  equations : Set (MvPolynomial (ULift.{u} (Fin n × Fin n)) k) :=
    {slDetPoly n - 1}

omit [IsAlgClosed k] in
/-- `evalPolynomial` commutes with the matrix determinant. -/
public lemma evalPolynomial_det (n : ℕ) (x : ULift.{u} (Fin n × Fin n) → k)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (ULift.{u} (Fin n × Fin n)) k)) :
    evalPolynomial x M.det =
      Matrix.det (fun i j => evalPolynomial x (M i j) : Matrix (Fin n) (Fin n) k) := by
  let m : Matrix (Fin n) (Fin n) k := fun i j => evalPolynomial x (M i j)
  change evalPolynomial x M.det = m.det
  rw [Matrix.det_apply', Matrix.det_apply']
  simp [evalPolynomial, m]

omit [IsAlgClosed k] in
/-- Evaluation of the determinant polynomial. -/
public lemma evalPolynomial_slDetPoly (n : ℕ)
    (x : ULift.{u} (Fin n × Fin n) → k) :
    evalPolynomial x (slDetPoly n) =
      Matrix.det ((fun i j : Fin n => x (ULift.up (i, j))) : Matrix (Fin n) (Fin n) k) := by
  unfold slDetPoly
  rw [evalPolynomial_det]
  simp [slEntryMatrix, evalPolynomial_X]

omit [IsAlgClosed k] in
/-- `evalPolynomial` commutes with the adjugate of a matrix. -/
public lemma evalPolynomial_adjugate (n : ℕ) (x : ULift.{u} (Fin n × Fin n) → k)
    (i j : Fin n) (M : Matrix (Fin n) (Fin n) (MvPolynomial (ULift.{u} (Fin n × Fin n)) k)) :
    evalPolynomial x ((Matrix.adjugate M) i j) =
      Matrix.adjugate (fun i' j' => evalPolynomial x (M i' j') : Matrix (Fin n) (Fin n) k) i j := by
  let A : Matrix (Fin n) (Fin n) k := fun i' j' => evalPolynomial x (M i' j')
  change evalPolynomial x ((Matrix.adjugate M) i j) = (Matrix.adjugate A) i j
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  let B : Matrix (Fin n) (Fin n) (MvPolynomial (ULift.{u} (Fin n × Fin n)) k) :=
    M.updateRow j (Pi.single i 1)
  change evalPolynomial x B.det = (A.updateRow j (Pi.single i 1)).det
  rw [evalPolynomial_det]
  congr 1
  funext l m
  change evalPolynomial x ((M.updateRow j (Pi.single i 1)) l m) =
    (A.updateRow j (Pi.single i 1)) l m
  rw [Matrix.updateRow_apply, Matrix.updateRow_apply,
    Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp [A, evalPolynomial]

omit [IsAlgClosed k] in
/-- Evaluation of an adjugate entry. -/
public lemma evalPolynomial_slAdjugate (n : ℕ)
    (x : ULift.{u} (Fin n × Fin n) → k) (i j : Fin n) :
    evalPolynomial x ((Matrix.adjugate (slEntryMatrix n)) i j) =
      Matrix.adjugate ((fun i' j' : Fin n => x (ULift.up (i', j'))) : Matrix (Fin n) (Fin n) k) i j := by
  rw [evalPolynomial_adjugate]
  simp [slEntryMatrix, evalPolynomial_X]

/-- Matrix component of an `SLₙ` point. -/
@[expose]
public def slPointMatrix (n : ℕ) (x : Variety.Point (slVariety k n)) :
    Matrix (Fin n) (Fin n) k :=
  fun i j => x.val (ULift.up (i, j))

/-- The matrix component of an `SLₙ` point has determinant one. -/
public lemma slPoint_det_eq_one (n : ℕ) (x : Variety.Point (slVariety k n)) :
    (slPointMatrix n x).det = 1 := by
  have h := x.isZero (slDetPoly n - 1) (by simp [slVariety])
  have hsum : evalPolynomial x.val (slDetPoly n) - 1 = 0 := by
    simpa [evalPolynomial] using h
  have h' : evalPolynomial x.val (slDetPoly n) = 1 := sub_eq_zero.mp hsum
  have hdet : Matrix.det ((fun i j : Fin n => x.val (ULift.up (i, j))) : Matrix (Fin n) (Fin n) k) = 1 := by
    simpa [evalPolynomial_slDetPoly] using h'
  have hdet' : (slPointMatrix n x).det = Matrix.det ((fun i j : Fin n => x.val (ULift.up (i, j))) : Matrix (Fin n) (Fin n) k) := by
    rfl
  rw [hdet']
  exact hdet

/-- Point equivalence for `SLₙ`. -/
@[expose]
public def slPointEquiv (n : ℕ) : Variety.Point (slVariety k n) ≃ Matrix.SpecialLinearGroup (Fin n) k where
  toFun := fun x => ⟨slPointMatrix n x, slPoint_det_eq_one n x⟩
  invFun := fun A => ⟨fun p : ULift.{u} (Fin n × Fin n) => A.1 p.down.1 p.down.2, by
    intro p hp
    simp at hp
    subst hp
    have hdet : Matrix.det ((fun i j : Fin n => A.1 i j) : Matrix (Fin n) (Fin n) k) = 1 := by
      exact (A.2 : A.1.det = 1)
    change evalPolynomial (fun p : ULift.{u} (Fin n × Fin n) => A.1 p.down.1 p.down.2)
      (slDetPoly n - 1) = 0
    rw [show evalPolynomial (fun p : ULift.{u} (Fin n × Fin n) => A.1 p.down.1 p.down.2)
          (slDetPoly n - 1) =
        evalPolynomial (fun p : ULift.{u} (Fin n × Fin n) => A.1 p.down.1 p.down.2)
          (slDetPoly n) - 1 by
          simp [evalPolynomial]]
    rw [evalPolynomial_slDetPoly]
    simp [hdet]⟩
  left_inv := by
    intro x
    apply Variety.Point.ext
    funext p
    rfl
  right_inv := by
    intro A
    apply Subtype.ext
    ext i j
    rfl

/-- Multiplication polynomials for `SLₙ`. -/
@[expose]
public noncomputable def slMulPoly (n : ℕ) : (slVariety k n).Coordinates →
    MvPolynomial ((slVariety k n).Coordinates ⊕ (slVariety k n).Coordinates) k :=
  fun p => match p.down with
  | (i, j) =>
      ∑ l : Fin n, MvPolynomial.X (Sum.inl (ULift.up (i, l))) *
        MvPolynomial.X (Sum.inr (ULift.up (l, j)))

/-- Inverse polynomials for `SLₙ`, using Cramer's formula with determinant one. -/
@[expose]
public noncomputable def slInvPoly (n : ℕ) : (slVariety k n).Coordinates →
    MvPolynomial ((slVariety k n).Coordinates) k :=
  fun p => match p.down with
  | (i, j) => (Matrix.adjugate (slEntryMatrix n)) i j

end

section
open LinearMap Submodule

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The algebraic group `SL(V)` for a finite-dimensional vector space, obtained
by transporting the determinant-one locus for `SLₙ` along a basis. -/
@[expose]
public noncomputable def slVarietyOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V] : Variety k :=
  slVariety k (Module.finrank k V)

/-- Matrix of `g` in the basis `e`, whose columns are the coordinates of `g (e j)`. -/
public noncomputable def slMatrixOfGL (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (g : LinearMap.GeneralLinearGroup k V) :
    Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k :=
  fun i j => e.repr (g.1 (e j)) i

omit [IsAlgClosed k] in
/-- Under the basis conjugation, the coordinates of `g (e j)` are the `j`-th column of `A`. -/
public lemma slConj_apply_basis_coord (V : Type v) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (A : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k)
    (j : Fin (Module.finrank k V)) (l : Fin (Module.finrank k V)) :
    e.repr (e.equivFun.symm (A.mulVec (e.equivFun (e j)))) l = A l j := by
  classical
  have hsingle : e.equivFun (e j) = Pi.single j (1 : k) := by
    funext l'
    rw [Module.Basis.equivFun_apply, Module.Basis.repr_self_apply]
    by_cases hjl : j = l'
    · simp [hjl]
    · simp [hjl, Ne.symm hjl]
  rw [hsingle]
  have hrepr : e.repr (e.equivFun.symm (A.mulVec (Pi.single j (1 : k)))) =
      A.mulVec (Pi.single j (1 : k)) := by
    have hsymm : e.equivFun.symm (A.mulVec (Pi.single j (1 : k))) =
        ∑ i, (A.mulVec (Pi.single j (1 : k))) i • e i :=
      Module.Basis.equivFun_symm_apply e (A.mulVec (Pi.single j (1 : k)))
    rw [hsymm]
    ext i
    simp [Module.Basis.repr_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [hbi]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ i))
  rw [hrepr]
  simp [Matrix.mulVec_single]

/-- Linear map corresponding to an `SL(V)` point, transported through the basis `e`. -/
@[expose]
public noncomputable def slToFunOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (slVarietyOf k V)) :
    {g : LinearMap.GeneralLinearGroup k V | (slMatrixOfGL k V e g).det = 1} :=
  ⟨LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm
    (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL (slPointEquiv (Module.finrank k V) x))), by
    change (slMatrixOfGL k V e (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm
      (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL (slPointEquiv (Module.finrank k V) x))))).det = 1
    have hmat : slMatrixOfGL k V e (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm
        (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL (slPointEquiv (Module.finrank k V) x)))) =
        ((slPointEquiv (Module.finrank k V) x) : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k) := by
      ext i j
      dsimp [slMatrixOfGL]
      change e.repr (e.equivFun.symm
          (((slPointEquiv (Module.finrank k V) x) : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k).mulVec
            (e.equivFun (e j)))) i =
        ((slPointEquiv (Module.finrank k V) x) : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k) i j
      exact slConj_apply_basis_coord V e
        ((slPointEquiv (Module.finrank k V) x) : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k) j i
    rw [hmat]
    exact (slPointEquiv (Module.finrank k V) x).2⟩

/-- The `SLₙ` point corresponding to a determinant-one linear map. -/
public noncomputable def slInvFunOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (g : {g : LinearMap.GeneralLinearGroup k V | (slMatrixOfGL k V e g).det = 1}) :
    Variety.Point (slVarietyOf k V) :=
  slPointEquiv (Module.finrank k V) |>.symm
    (⟨slMatrixOfGL k V e g.1, g.2⟩ : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k)

/-- Point equivalence `SL(V) = {g : GL(V) | det (matrix of g) = 1}` in the basis `e`. -/
public noncomputable def slPointEquivOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    Variety.Point (slVarietyOf k V) ≃
      {g : LinearMap.GeneralLinearGroup k V | (slMatrixOfGL k V e g).det = 1} :=
  ⟨slToFunOf k V e, slInvFunOf k V e,
   by
    intro x
    let a : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k :=
      ⟨slMatrixOfGL k V e (slToFunOf k V e x).1, (slToFunOf k V e x).2⟩
    apply (slPointEquiv (Module.finrank k V)).injective
    change (slPointEquiv (Module.finrank k V)) ((slPointEquiv (Module.finrank k V)).symm a) =
      slPointEquiv (Module.finrank k V) x
    rw [(slPointEquiv (Module.finrank k V)).apply_symm_apply]
    apply Subtype.ext
    change slMatrixOfGL k V e (slToFunOf k V e x).1 =
      ((slPointEquiv (Module.finrank k V) x) : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k)
    dsimp [slToFunOf]
    ext i j
    dsimp [slMatrixOfGL]
    change e.repr (e.equivFun.symm
        (((slPointEquiv (Module.finrank k V) x) : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k).mulVec
          (e.equivFun (e j)))) i =
      ((slPointEquiv (Module.finrank k V) x) : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k) i j
    exact slConj_apply_basis_coord V e
      ((slPointEquiv (Module.finrank k V) x) : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k) j i,
   by
    intro g
    apply Subtype.ext
    apply Units.ext
    dsimp [slInvFunOf, slToFunOf]
    have hSymm : slPointEquiv (Module.finrank k V) ((slPointEquiv (Module.finrank k V)).symm
        (⟨slMatrixOfGL k V e g.1, g.2⟩ : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k)) =
        (⟨slMatrixOfGL k V e g.1, g.2⟩ : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k) :=
      (slPointEquiv (Module.finrank k V)).apply_symm_apply _
    rw [hSymm]
    change (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm
      (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL
        (⟨slMatrixOfGL k V e g.1, g.2⟩ : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k)))).1 = g.1.1
    apply LinearMap.ext
    intro v
    have hv : v = e.equivFun.symm (e.equivFun v) := by
      rw [Module.Basis.equivFun_symm_apply]
      exact (Module.Basis.sum_equivFun e v).symm
    rw [hv]
    rw [Module.Basis.equivFun_symm_apply]
    simp_rw [map_sum, LinearMap.map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg (fun c => (e.equivFun v) j • c)
    apply (e.repr).injective
    ext l
    change e.repr (e.equivFun.symm
        (((⟨slMatrixOfGL k V e g.1, g.2⟩ : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k).1).mulVec
          (e.equivFun (e j)))) l =
      e.repr (g.1.1 (e j)) l
    rw [slConj_apply_basis_coord V e
      (⟨slMatrixOfGL k V e g.1, g.2⟩ : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k).1 j l]
    have hright : e.repr (g.1.1 (e j)) l =
        (⟨slMatrixOfGL k V e g.1, g.2⟩ : Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k).1 l j := by
      rfl
    rw [hright]⟩

end

section

/-- The algebraic-group structure on `SLₙ`. -/
public noncomputable instance slAlgebraicGroup (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) : AlgebraicGroup (slVariety k n) := by
  let e := slPointEquiv (k := k) n
  let hGroup : Group (Variety.Point (slVariety k n)) := e.group
  letI : Group (Variety.Point (slVariety k n)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := slMulPoly n
      invPolynomial := slInvPoly n
      mul_regular := by
        intro p x y
        rcases p with ⟨⟨i, j⟩⟩
        change (x * y).val (ULift.up (i, j)) = evalPolynomial (Sum.elim x.val y.val)
            (slMulPoly n (ULift.up (i, j)))
        simp [slMulPoly, evalPolynomial]
        change (e.symm (e x * e y)).val (ULift.up (i, j)) =
          ∑ l : Fin n, x.val (ULift.up (i, l)) * y.val (ULift.up (l, j))
        have hz : ∀ z : Matrix.SpecialLinearGroup (Fin n) k,
            (e.symm z).val (ULift.up (i, j)) = z.1 i j := by
          intro z
          rfl
        rw [hz]
        rfl
      inv_regular := by
        intro p x
        rcases p with ⟨⟨i, j⟩⟩
        change x⁻¹.val (ULift.up (i, j)) = evalPolynomial x.val (slInvPoly n (ULift.up (i, j)))
        rw [slInvPoly, evalPolynomial_slAdjugate]
        change (e.symm (e x)⁻¹).val (ULift.up (i, j)) =
          Matrix.adjugate ((fun i' j' : Fin n => x.val (ULift.up (i', j'))) : Matrix (Fin n) (Fin n) k) i j
        have hz : ∀ z : Matrix.SpecialLinearGroup (Fin n) k,
            (e.symm z).val (ULift.up (i, j)) = z.1 i j := by
          intro z
          rfl
        rw [hz]
        have hmul : ((e x)⁻¹).1 * (e x).1 = (1 : Matrix (Fin n) (Fin n) k) := by
          have hmu : (e x)⁻¹ * (e x) = 1 := by simp
          calc
            ((e x)⁻¹).1 * (e x).1 = ↑((e x)⁻¹ * (e x)) := by rfl
            _ = (1 : Matrix (Fin n) (Fin n) k) := by rw [hmu]; rfl
        have hiv : ((e x)⁻¹).1 = ((e x).1 : Matrix (Fin n) (Fin n) k)⁻¹ :=
          (Matrix.inv_eq_left_inv (A := (e x).1) (B := ((e x)⁻¹).1) hmul).symm
        rw [hiv]
        have hval1 : (e x).1 = slPointMatrix n x := by
          change (⟨slPointMatrix n x, slPoint_det_eq_one n x⟩ : Matrix.SpecialLinearGroup (Fin n) k).1 =
            slPointMatrix n x
          rfl
        rw [hval1]
        rw [Matrix.nonsing_inv_apply (A := slPointMatrix n x) (by
          exact (slPoint_det_eq_one n x).symm ▸ isUnit_one)]
        simp [slPoint_det_eq_one n x]
        change Matrix.adjugate (slPointMatrix n x) i j =
          Matrix.adjugate ((fun i' j' : Fin n => x.val (ULift.up (i', j'))) : Matrix (Fin n) (Fin n) k) i j
        rfl }

end

section

public noncomputable instance slAlgebraicGroupOf (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    AlgebraicGroup (slVarietyOf k V) := by
  change AlgebraicGroup (slVariety k (Module.finrank k V))
  exact slAlgebraicGroup k (Module.finrank k V)

end

end Theory.AlgebraicGroup
