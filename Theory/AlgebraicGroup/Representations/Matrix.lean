module

public import Mathlib.RepresentationTheory.Basic
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.CoordinateRing.PolynomialFunction
public import Theory.AlgebraicGroup.Morphism.Operations
public import Theory.AlgebraicGroup.Representations.Rational

universe u v w

/-! Matrix-coordinate identities for finite-dimensional representations. -/

/-! Determinant of the matrix of an inverse linear automorphism. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

public lemma generalLinear_toMatrix_inv_det
    (b : Module.Basis ι k V) (x : LinearMap.GeneralLinearGroup k V) :
    (LinearMap.toMatrix b b
      ((x⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V)).det =
      (LinearMap.toMatrix b b (x : Module.End k V)).det⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← Matrix.det_mul, ← LinearMap.toMatrix_mul]
  have h := congrArg
    (fun z : LinearMap.GeneralLinearGroup k V => (z : Module.End k V))
    (show x⁻¹ * x = 1 by simp)
  have hcoe : (↑(x⁻¹ * x) : Module.End k V) =
      (↑x⁻¹ : Module.End k V) * (↑x : Module.End k V) := rfl
  have h' : (↑x⁻¹ : Module.End k V) * (↑x : Module.End k V) = 1 := by
    rw [← hcoe, h]
    rfl
  have hmat := congrArg (fun z : Module.End k V => LinearMap.toMatrix b b z) h'
  rw [hmat, LinearMap.toMatrix_one, Matrix.det_one]

end

/-! The point representation underlying a closed-subgroup morphism to `GLₙ`. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.generalLinearMorphismRepresentation
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) (n : ℕ)
    (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k)) :
    Representation k K.toSubgroup (Fin n → k) := by
  let eK : Variety.Point K.carrierVariety ≃* K.toSubgroup :=
    { toEquiv := K.pointEquiv
      map_mul' := fun _ _ => rfl }
  let glAction : K.toSubgroup →* LinearMap.GeneralLinearGroup k (Fin n → k) :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := k)).toMonoidHom.comp
      ((translationGLPointMulEquiv n).toMonoidHom.comp
        (ρ.onPoints.comp eK.symm.toMonoidHom))
  exact (Units.coeHom (Module.End k (Fin n → k))).comp glAction

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.generalLinearMorphismRepresentation_matrixCoefficient
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) (n : ℕ)
    (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (s : K.toSubgroup) (i j : Fin n) :
    (Pi.basisFun k (Fin n)).repr
      (K.generalLinearMorphismRepresentation n ρ s
        ((Pi.basisFun k (Fin n)) j)) i =
      (ρ.onPoints (K.pointEquiv.symm s)).val (Sum.inl (i, j)) := by
  rw [Pi.basisFun_apply]
  dsimp [ClosedSubgroup.generalLinearMorphismRepresentation]
  change (Matrix.mulVec (glPointEquiv n (ρ.onPoints (K.pointEquiv.symm s)) :
    Matrix (Fin n) (Fin n) k) (Pi.single j 1)) i = _
  simp [glPointEquiv, glMatrixOfPoint, Matrix.mulVec_single]

end

/-! A coordinate formula for a linear map in a fixed basis. -/

section

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

public lemma LinearMap.repr_apply_eq_sum_toMatrix
    (b : Module.Basis ι k V) (f : Module.End k V) (v : V) (i : ι) :
    ∑ j, (b.repr v) j * (LinearMap.toMatrix b b f) i j = (b.repr (f v)) i := by
  have h := congrFun (LinearMap.toMatrix_mulVec_repr b b f v) i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end

/-! Expanding a matrix coefficient against a fixed basis. -/

section

open scoped BigOperators

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

public lemma LinearMap.dual_apply_eq_sum_toMatrix
    (b : Module.Basis ι k V) (L : Module.Dual k V)
    (f : Module.End k V) (x : V) :
    (∑ p, ∑ q, L (b p) * (b.repr x q) * (LinearMap.toMatrix b b f) p q) =
      L (f x) := by
  calc
    (∑ p, ∑ q, L (b p) * (b.repr x q) * (LinearMap.toMatrix b b f) p q) =
        ∑ p, L (b p) * (b.repr (f x) p) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [← LinearMap.repr_apply_eq_sum_toMatrix b f x p]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
    _ = ∑ p, (b.repr (f x) p) * L (b p) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = ∑ p, L ((b.repr (f x) p) • b p) := by simp
    _ = L (∑ p, (b.repr (f x) p) • b p) := by rw [map_sum]
    _ = L (f x) := by rw [b.sum_repr]

end

/-! Coordinates of the general-linear variety point attached to a linear automorphism. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]

@[expose]
public noncomputable def generalLinearRepresentationPoint
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : LinearMap.GeneralLinearGroup k V) :
    Variety.Point (glVariety (Module.finrank k V) : Variety k) :=
  (translationGLPointMulEquiv (Module.finrank k V)).symm
    ((Matrix.GeneralLinearGroup.toLin'
      (n := Fin (Module.finrank k V)) (R := k) (V := V) b).symm x)

omit [IsAlgClosed k] [Module.Finite k V] in
public lemma generalLinearRepresentationPoint_matrix
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : LinearMap.GeneralLinearGroup k V)
    (i j : Fin (Module.finrank k V)) :
    (generalLinearRepresentationPoint b x).val (Sum.inl (i, j)) =
      b.repr ((x : Module.End k V) (b j)) i := by
  rw [generalLinearRepresentationPoint, translationGLPointMulEquiv]
  let M : GL (Fin (Module.finrank k V)) k :=
    (Matrix.GeneralLinearGroup.toLin' b).symm x
  change (M : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k) i j = _
  have hx : Matrix.GeneralLinearGroup.toLin' b M = x :=
    (Matrix.GeneralLinearGroup.toLin' b).apply_symm_apply x
  have h := congrArg
    (fun y : LinearMap.GeneralLinearGroup k V => b.repr (y.toLinearEquiv (b j)) i) hx
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at h
  simpa [Fintype.linearCombination_apply, Matrix.mulVec, dotProduct,
    Finsupp.single_apply] using h

omit [IsAlgClosed k] [Module.Finite k V] in
public lemma generalLinearRepresentationPoint_scalar
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : LinearMap.GeneralLinearGroup k V) :
    (generalLinearRepresentationPoint b x).val (Sum.inr PUnit.unit) =
      (LinearMap.toMatrix b b (x : Module.End k V)).det⁻¹ := by
  change glScalarOfPoint (Module.finrank k V)
    (generalLinearRepresentationPoint b x) = _
  rw [glScalarOfPoint_eq_inv_det]
  congr 1

omit [IsAlgClosed k] [Module.Finite k V] in
public lemma generalLinearRepresentationPoint_one
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    generalLinearRepresentationPoint b 1 = 1 := by
  simp [generalLinearRepresentationPoint]

omit [IsAlgClosed k] [Module.Finite k V] in
public lemma generalLinearRepresentationPoint_eq_one_iff
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : LinearMap.GeneralLinearGroup k V) :
    generalLinearRepresentationPoint b x = 1 ↔ x = 1 := by
  constructor
  · intro h
    have h' := congrArg (translationGLPointMulEquiv (Module.finrank k V)) h
    simpa [generalLinearRepresentationPoint] using h'
  · rintro rfl
    exact generalLinearRepresentationPoint_one b

omit [IsAlgClosed k] [Module.Finite k V] in
public lemma generalLinearRepresentationPoint_mul
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x y : LinearMap.GeneralLinearGroup k V) :
    generalLinearRepresentationPoint b (x * y) =
      generalLinearRepresentationPoint b x * generalLinearRepresentationPoint b y := by
  simp [generalLinearRepresentationPoint]

end

/-! A regular general-linear representation assembled from regular coordinates. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]

@[expose]
public noncomputable def generalLinearRepresentationMorphism
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k V)
    (matrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → G.PolynomialFunction)
    (matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g = b.repr ((ρ g : Module.End k V) (b j)) i)
    (inverseDeterminant : G.PolynomialFunction)
    (inverseDeterminant_apply : ∀ g,
      inverseDeterminant g =
        (LinearMap.toMatrix b b (ρ g : Module.End k V)).det⁻¹) :
    AlgebraicGroup.Morphism G (glVariety (Module.finrank k V) : Variety k) where
  toVariety :=
    { toFun := fun g => generalLinearRepresentationPoint b (ρ g)
      regular := by
        intro c
        cases c with
        | inl ij =>
            rcases ij with ⟨i, j⟩
            rcases (matrixCoefficient i j).representedBy with ⟨p, hp⟩
            refine ⟨p, fun g => ?_⟩
            rw [← hp g]
            calc
              (generalLinearRepresentationPoint b (ρ g)).val (Sum.inl (i, j)) =
                  b.repr ((ρ g : Module.End k V) (b j)) i :=
                generalLinearRepresentationPoint_matrix b (ρ g) i j
              _ = matrixCoefficient i j g := (matrixCoefficient_apply i j g).symm
        | inr q =>
            cases q
            rcases inverseDeterminant.representedBy with ⟨p, hp⟩
            refine ⟨p, fun g => ?_⟩
            rw [← hp g]
            calc
              (generalLinearRepresentationPoint b (ρ g)).val (Sum.inr PUnit.unit) =
                  (LinearMap.toMatrix b b (ρ g : Module.End k V)).det⁻¹ :=
                generalLinearRepresentationPoint_scalar b (ρ g)
              _ = inverseDeterminant g := (inverseDeterminant_apply g).symm }
  map_one := by
    simpa using generalLinearRepresentationPoint_one b
  map_mul := by
    intro g h
    simpa using generalLinearRepresentationPoint_mul b (ρ g) (ρ h)

omit [IsAlgClosed k] [Module.Finite k V] in
public lemma generalLinearRepresentationMorphism_apply
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k V)
    (matrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → G.PolynomialFunction)
    (matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g = b.repr ((ρ g : Module.End k V) (b j)) i)
    (inverseDeterminant : G.PolynomialFunction)
    (inverseDeterminant_apply : ∀ g,
      inverseDeterminant g =
        (LinearMap.toMatrix b b (ρ g : Module.End k V)).det⁻¹)
    (g : Variety.Point G) :
    (generalLinearRepresentationMorphism b ρ matrixCoefficient matrixCoefficient_apply
      inverseDeterminant inverseDeterminant_apply).onPoints g =
      generalLinearRepresentationPoint b (ρ g) :=
  rfl

end

/-! Matrix-coordinate polynomial functions on the general-linear variety. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def generalLinearMatrixCoordinate (n : ℕ)
    (i j : Fin n) : (glVariety n : Variety k).PolynomialFunction :=
  Variety.PolynomialFunction.ofPolynomial (glVariety n : Variety k)
    (MvPolynomial.X (Sum.inl (i, j)))

omit [IsAlgClosed k] in
public lemma generalLinearMatrixCoordinate_apply (n : ℕ) (i j : Fin n)
    (x : Variety.Point (glVariety n : Variety k)) :
    generalLinearMatrixCoordinate (k := k) n i j x = x.val (Sum.inl (i, j)) := by
  change evalPolynomial x.val (MvPolynomial.X (Sum.inl (i, j))) = _
  simp [evalPolynomial]

@[expose]
public noncomputable def generalLinearInverseMatrixCoordinate (n : ℕ)
    (i j : Fin n) : (glVariety n : Variety k).PolynomialFunction :=
  Variety.PolynomialFunction.pullback
    (AlgebraicGroup.invMorphism (glVariety n : Variety k))
    (generalLinearMatrixCoordinate (k := k) n i j)

omit [IsAlgClosed k] in
public lemma generalLinearInverseMatrixCoordinate_apply (n : ℕ) (i j : Fin n)
    (x : Variety.Point (glVariety n : Variety k)) :
    generalLinearInverseMatrixCoordinate (k := k) n i j x =
      x⁻¹.val (Sum.inl (i, j)) := by
  exact generalLinearMatrixCoordinate_apply n i j x⁻¹

end

/-! Matrix coefficients of rational representations. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

@[expose]
public noncomputable def rationalRepresentationMatrixCoefficient
    (_ρ : RationalRepresentation G V)
    (_e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) : G.PolynomialFunction :=
  Variety.PolynomialFunction.pullback f.toVariety
    (generalLinearMatrixCoordinate (Module.finrank k V) i j)

public lemma rationalRepresentationMatrixCoefficient_apply
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (i j : Fin (Module.finrank k V)) (g : Variety.Point G) :
    rationalRepresentationMatrixCoefficient ρ e f i j g =
      e.repr ((ρ.action g : Module.End k V) (e j)) i := by
  rw [rationalRepresentationMatrixCoefficient]
  change (generalLinearMatrixCoordinate (Module.finrank k V) i j)
    (f.onPoints g : Variety.Point (glVariety (Module.finrank k V) : Variety k)) = _
  unfold generalLinearMatrixCoordinate
  unfold Variety.PolynomialFunction.ofPolynomial
    Variety.PolynomialFunction.toFun evalPolynomial
  simp only [MvPolynomial.eval₂_X]
  change glMatrixOfPoint (Module.finrank k V) (f.onPoints g) i j = _
  have hb := glPointEquivOf_apply_basis V e (f.onPoints g) j
  rw [hf g] at hb
  have hc := congrArg (e.coord i) hb
  rw [Module.Basis.coord_equivFun_symm] at hc
  exact hc.symm

@[expose]
public noncomputable def rationalRepresentationInverseMatrixCoefficient
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) : G.PolynomialFunction :=
  Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
    (rationalRepresentationMatrixCoefficient ρ e f i j)

@[expose]
public noncomputable def rationalRepresentationLinearMatrixCoefficient
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (l : Module.Dual k V) (v : V) : G.PolynomialFunction :=
  ∑ i, ∑ j, algebraMap k G.PolynomialFunction (l (e i) * e.repr v j) *
    rationalRepresentationMatrixCoefficient ρ e f i j

public lemma rationalRepresentationLinearMatrixCoefficient_apply
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (l : Module.Dual k V) (v : V) (g : Variety.Point G) :
    rationalRepresentationLinearMatrixCoefficient ρ e f l v g =
      l ((ρ.action g : Module.End k V) v) := by
  rw [rationalRepresentationLinearMatrixCoefficient]
  let ev : G.PolynomialFunction →+* k :=
    { toFun := fun q => q g
      map_one' := by
        rw [← (algebraMap k (Variety.PolynomialFunction G)).map_one]
        exact polynomialFunction_algebraMap_apply G 1 g
      map_mul' := by
        intro x y
        change (x * y) g = x g * y g
        rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i, ∑ j,
    algebraMap k G.PolynomialFunction (l (e i) * e.repr v j) *
      rationalRepresentationMatrixCoefficient ρ e f i j) = _
  rw [map_sum]
  simp_rw [map_sum, map_mul]
  have hev (q : G.PolynomialFunction) : ev q = q g := rfl
  simp_rw [hev]
  simp_rw [polynomialFunction_algebraMap_apply]
  simp_rw [rationalRepresentationMatrixCoefficient_apply ρ e f hf]
  simpa [LinearMap.toMatrix_apply] using
    LinearMap.dual_apply_eq_sum_toMatrix e l (ρ.action g : Module.End k V) v

public lemma glPointEquivOf_generalLinearRepresentationPoint
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : LinearMap.GeneralLinearGroup k V) :
    glPointEquivOf k V b (generalLinearRepresentationPoint b x) = x := by
  apply Units.ext
  apply b.ext
  intro j
  have hb := glPointEquivOf_apply_basis V b
    (generalLinearRepresentationPoint b x : Variety.Point (glVarietyOf k V)) j
  rw [hb]
  let c : Fin (Module.finrank k V) → k := fun l =>
    glMatrixOfPoint (Module.finrank k V)
      (generalLinearRepresentationPoint b x) l j
  change b.equivFun.symm c = (x : Module.End k V) (b j)
  apply b.equivFun.injective
  funext i
  rw [b.equivFun.apply_symm_apply, b.equivFun_apply]
  change glMatrixOfPoint (Module.finrank k V)
    (generalLinearRepresentationPoint b x) i j = _
  exact generalLinearRepresentationPoint_matrix b x i j

public lemma rationalRepresentationInverseMatrixCoefficient_apply
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (i j : Fin (Module.finrank k V)) (g : Variety.Point G) :
    rationalRepresentationInverseMatrixCoefficient ρ e f i j g =
      e.repr (((((ρ.action g)⁻¹ : LinearMap.GeneralLinearGroup k V) :
        Module.End k V)) (e j)) i := by
  rw [rationalRepresentationInverseMatrixCoefficient]
  change rationalRepresentationMatrixCoefficient ρ e f i j g⁻¹ = _
  rw [rationalRepresentationMatrixCoefficient_apply ρ e f hf]
  simp

end

/-! Assemble a regular general-linear morphism from matrix coefficients and
inverse matrix coefficients. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]

@[expose]
public noncomputable def generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k V)
    (matrixCoefficient inverseMatrixCoefficient :
      Fin (Module.finrank k V) → Fin (Module.finrank k V) →
        G.PolynomialFunction)
    (matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g = b.repr ((ρ g : Module.End k V) (b j)) i)
    (inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr ((((ρ g)⁻¹ : LinearMap.GeneralLinearGroup k V) :
          Module.End k V) (b j)) i) :
    AlgebraicGroup.Morphism G (glVariety (Module.finrank k V) : Variety k) :=
  let invM : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V))
      G.PolynomialFunction := fun i j => inverseMatrixCoefficient i j
  generalLinearRepresentationMorphism b ρ matrixCoefficient
    matrixCoefficient_apply (Matrix.det invM) (by
      intro g
      let ev : G.PolynomialFunction →+* k :=
        { toFun := fun f => f g
          map_one' := by
            rw [← (algebraMap k (Variety.PolynomialFunction G)).map_one]
            exact polynomialFunction_algebraMap_apply G 1 g
          map_mul' := by
            intro x y
            change (x * y) g = x g * y g
            rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hEval : Matrix.det invM g =
          (LinearMap.toMatrix b b
            ((((ρ g)⁻¹ : LinearMap.GeneralLinearGroup k V) :
              Module.End k V))).det := by
        change ev (Matrix.det invM) = _
        rw [RingHom.map_det]
        congr 1
        funext i j
        change invM i j g = _
        change inverseMatrixCoefficient i j g = _
        rw [LinearMap.toMatrix_apply]
        exact inverseMatrixCoefficient_apply i j g
      rw [hEval]
      exact generalLinear_toMatrix_inv_det b (ρ g))

omit [IsAlgClosed k] [Module.Finite k V] in
public lemma generalLinearRepresentationMorphismOfInverseMatrixCoefficient_apply
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k V)
    (matrixCoefficient inverseMatrixCoefficient :
      Fin (Module.finrank k V) → Fin (Module.finrank k V) →
        G.PolynomialFunction)
    (matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g = b.repr ((ρ g : Module.End k V) (b j)) i)
    (inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr ((((ρ g)⁻¹ : LinearMap.GeneralLinearGroup k V) :
          Module.End k V) (b j)) i)
    (g : Variety.Point G) :
    (generalLinearRepresentationMorphismOfInverseMatrixCoefficient b ρ
      matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply).onPoints g =
      generalLinearRepresentationPoint b (ρ g) :=
  rfl

end

end Theory.AlgebraicGroup
