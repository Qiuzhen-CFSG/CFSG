module

public import Theory.AlgebraicGroup.Instance.Triangular
public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding
public import Theory.AlgebraicGroup.Representations.Matrix

universe u v

/-! Rational representations written in an upper-triangular basis. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A rational representation which is upper triangular in one basis defines
an algebraic-group morphism to the corresponding triangular group. -/
@[expose]
public noncomputable def triangularRepresentationMorphismOfBasis
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (htri : ∀ g, tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V))) :
    AlgebraicGroup.Morphism G (tVariety k (Module.finrank k V)) := by
  let e : Module.Basis (Fin (Module.finrank k V)) k V := Classical.choose hρ
  have hρ' : ∃ f : AlgebraicGroup.Morphism G (glVarietyOf k V),
      ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g := by
    simpa [e] using Classical.choose_spec hρ
  let f : AlgebraicGroup.Morphism G (glVarietyOf k V) := Classical.choose hρ'
  have hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g := by
    simpa [f] using Classical.choose_spec hρ'
  let coefficient : Fin (Module.finrank k V) → Fin (Module.finrank k V) →
      G.PolynomialFunction := fun i j =>
    rationalRepresentationLinearMatrixCoefficient ρ e f (b.dualBasis i) (b j)
  have coefficient_apply : ∀ i j g,
      coefficient i j g =
        LinearMap.toMatrix b b (ρ.action g : Module.End k V) i j := by
    intro i j g
    rw [show coefficient i j =
      rationalRepresentationLinearMatrixCoefficient ρ e f
        (b.dualBasis i) (b j) by rfl]
    rw [rationalRepresentationLinearMatrixCoefficient_apply ρ e f hf]
    rw [LinearMap.toMatrix_apply]
    exact b.dualBasis_apply i ((ρ.action g : Module.End k V) (b j))
  have triangularGL_matrix : ∀ g : Variety.Point G,
      (((Matrix.GeneralLinearGroup.toLin' b).symm (ρ.action g) :
          GL (Fin (Module.finrank k V)) k) :
        Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k) =
        LinearMap.toMatrix b b (ρ.action g : Module.End k V) := by
    intro g
    rfl
  let triangularGL (g : Variety.Point G) : tTriangularGL k (Module.finrank k V) :=
    ⟨(Matrix.GeneralLinearGroup.toLin' b).symm (ρ.action g), by
      change tTriangular (Module.finrank k V)
        (((Matrix.GeneralLinearGroup.toLin' b).symm (ρ.action g) :
          GL (Fin (Module.finrank k V)) k) :
          Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k)
      exact htri g⟩
  let triangularPoint (g : Variety.Point G) :
      Variety.Point (tVariety k (Module.finrank k V)) :=
    (tPointEquiv k (Module.finrank k V)).symm (triangularGL g)
  exact
    { toVariety :=
        { toFun := triangularPoint
          regular := by
            intro p
            cases p with
            | inl q =>
                rcases (coefficient q.down.1 q.down.2).representedBy with ⟨P, hP⟩
                refine ⟨P, fun g => ?_⟩
                rw [← hP g]
                have hcoord :
                    (triangularPoint g).val (Sum.inl q) =
                      coefficient q.down.1 q.down.2 g := by
                  simp [triangularPoint, triangularGL, tPointEquiv_symm_val_inl]
                  rw [triangularGL_matrix g, coefficient_apply]
                exact hcoord
            | inr q =>
                let inverseDiagonal : G.PolynomialFunction :=
                  Variety.PolynomialFunction.pullback
                    (AlgebraicGroup.invMorphism G) (coefficient q.down q.down)
                rcases inverseDiagonal.representedBy with ⟨P, hP⟩
                refine ⟨P, fun g => ?_⟩
                rw [← hP g]
                have hGL_inv : triangularGL (g⁻¹) = (triangularGL g)⁻¹ := by
                  apply Subtype.ext
                  ext i j
                  simp [triangularGL, map_inv]
                have hcoord :
                    (triangularPoint g).val (Sum.inr q) = inverseDiagonal g := by
                  calc
                    (triangularPoint g).val (Sum.inr q) =
                        ((triangularGL g).1.1 q.down q.down)⁻¹ := by
                      simp [triangularPoint, triangularGL, tPointEquiv_symm_val_inr]
                    _ = ((triangularGL (g⁻¹)).1.1 q.down q.down) := by
                      rw [← tTriangularGL_inv_diag (n := Module.finrank k V)
                        (A := triangularGL g) q.down, hGL_inv]
                    _ = inverseDiagonal g := by
                      have hmat := congrArg (fun M => M q.down q.down)
                        (triangularGL_matrix (g⁻¹))
                      rw [hmat]
                      have hdiag : inverseDiagonal g =
                          (coefficient q.down q.down).toFun g⁻¹ := by
                        rfl
                      rw [hdiag]
                      exact (coefficient_apply q.down q.down (g⁻¹)).symm
                exact hcoord }
      map_one := by
        apply (tPointEquiv k (Module.finrank k V)).injective
        simp [triangularPoint, triangularGL, tPointEquiv_one]
      map_mul := by
        intro g h
        apply (tPointEquiv k (Module.finrank k V)).injective
        simp [triangularPoint, triangularGL, tPointEquiv_mul] }

/-- Pointwise, the triangular representation morphism is the original action
written in the chosen upper-triangular basis. -/
public lemma triangularRepresentationMorphismOfBasis_pointEquiv
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (htri : ∀ g, tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)))
    (g : Variety.Point G) :
    tPointEquiv k (Module.finrank k V)
      ((triangularRepresentationMorphismOfBasis ρ hρ b htri).onPoints g) =
      ⟨(Matrix.GeneralLinearGroup.toLin' b).symm (ρ.action g), by
        change tTriangular (Module.finrank k V)
          (((Matrix.GeneralLinearGroup.toLin' b).symm (ρ.action g) :
            GL (Fin (Module.finrank k V)) k) :
            Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k)
        exact htri g⟩ := by
  simp [triangularRepresentationMorphismOfBasis, AlgebraicGroup.Morphism.onPoints]

/-- If the underlying rational representation is faithful on points, then the
associated triangularized morphism is faithful on points as well. -/
public lemma triangularRepresentationMorphismOfBasis_injective
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (htri : ∀ g, tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)))
    (hinj : Function.Injective ρ.action) :
    Function.Injective
      (triangularRepresentationMorphismOfBasis ρ hρ b htri).onPoints := by
  intro x y hxy
  apply hinj
  have hpt := congrArg (tPointEquiv k (Module.finrank k V)) hxy
  simpa [triangularRepresentationMorphismOfBasis_pointEquiv] using hpt

/-- A matrix-entry coordinate on an upper-triangular target. -/
@[expose]
public noncomputable def triangularMatrixCoordinate (n : ℕ) (i j : Fin n) :
    Variety.PolynomialFunction (tVariety k n) :=
  Variety.PolynomialFunction.ofPolynomial _
    (MvPolynomial.X (Sum.inl (ULift.up (i, j))))

/-- Pullback of a triangular matrix coordinate is the corresponding matrix
entry of the represented action in the adapted basis. -/
public lemma triangularMatrixCoordinate_apply
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (htri : ∀ g, tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)))
    (i j : Fin (Module.finrank k V)) (g : Variety.Point G) :
    triangularMatrixCoordinate (k := k) (Module.finrank k V) i j
      ((triangularRepresentationMorphismOfBasis ρ hρ b htri).onPoints g) =
      LinearMap.toMatrix b b (ρ.action g : Module.End k V) i j := by
  simp only [triangularMatrixCoordinate, Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun, evalPolynomial, MvPolynomial.eval₂_X]
  let x := (triangularRepresentationMorphismOfBasis ρ hρ b htri).onPoints g
  calc
    x.val (Sum.inl (ULift.up (i, j))) =
        ((tPointEquiv k (Module.finrank k V)).symm
          (tPointEquiv k (Module.finrank k V) x)).val
            (Sum.inl (ULift.up (i, j))) := by
      rw [Equiv.symm_apply_apply]
    _ = (tPointEquiv k (Module.finrank k V) x).1.1 i j :=
      tPointEquiv_symm_val_inl (k := k) (Module.finrank k V)
        (tPointEquiv k (Module.finrank k V) x) (ULift.up (i, j))
    _ = _ := by
      rw [triangularRepresentationMorphismOfBasis_pointEquiv]
      rfl

/-- A linear matrix coefficient written as a polynomial function on the
upper-triangular target in an arbitrary adapted basis. -/
@[expose]
public noncomputable def triangularLinearMatrixCoefficientPreimage
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (K : Module.Dual k V) (v : V) :
    Variety.PolynomialFunction (tVariety k (Module.finrank k V)) :=
  ∑ j, b.repr v j •
    ∑ i, K (b i) • triangularMatrixCoordinate (k := k) (Module.finrank k V) i j

/-- Evaluation of an arbitrary-basis triangular matrix coefficient. -/
public lemma triangularLinearMatrixCoefficientPreimage_apply
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (htri : ∀ g, tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)))
    (K : Module.Dual k V) (v : V) (g : Variety.Point G) :
    triangularLinearMatrixCoefficientPreimage (k := k) b K v
      ((triangularRepresentationMorphismOfBasis ρ hρ b htri).onPoints g) =
      K ((ρ.action g : Module.End k V) v) := by
  have hK (x : V) : ∑ i, K (b i) * b.repr x i = K x := by
    calc
      ∑ i, K (b i) * b.repr x i =
          ∑ i, b.repr x i * K (b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm]
      _ = K (∑ i, b.repr x i • b i) := by
        rw [map_sum]
        simp [smul_eq_mul]
      _ = K x := by rw [b.sum_repr]
  have hsum (j) :
      (∑ i, K (b i) • triangularMatrixCoordinate (k := k)
        (Module.finrank k V) i j)
          ((triangularRepresentationMorphismOfBasis ρ hρ b htri).onPoints g) =
      ∑ i, K (b i) *
        LinearMap.toMatrix b b (ρ.action g : Module.End k V) i j := by
    change polynomialFunctionEvalAddHom _ _
      (∑ i, K (b i) • triangularMatrixCoordinate (k := k)
        (Module.finrank k V) i j) = _
    rw [map_sum]
    simp only [polynomialFunctionEvalAddHom_apply, polynomialFunction_smul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact triangularMatrixCoordinate_apply ρ hρ b htri i j g
  change polynomialFunctionEvalAddHom _ _
    (∑ j, b.repr v j •
      ∑ i, K (b i) • triangularMatrixCoordinate (k := k)
        (Module.finrank k V) i j) = _
  rw [map_sum]
  simp_rw [polynomialFunctionEvalAddHom_apply, polynomialFunction_smul_apply, hsum]
  simp_rw [LinearMap.toMatrix_apply, hK]
  calc
    ∑ j, b.repr v j * K ((ρ.action g : Module.End k V) (b j)) =
        K (∑ j, b.repr v j • (ρ.action g : Module.End k V) (b j)) := by
      rw [map_sum]
      simp [smul_eq_mul]
    _ = K ((ρ.action g : Module.End k V) (∑ j, b.repr v j • b j)) := by
      congr 1
      rw [map_sum]
      simp
    _ = K ((ρ.action g : Module.End k V) v) := by rw [b.sum_repr]

/-- Coordinate preimages make a faithful triangularized representation an
algebraic-group isomorphism onto its closed image. -/
public lemma triangularRepresentationMorphismOfBasis_iso_imageClosedSubgroup
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (htri : ∀ g, tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)))
    (hinj : Function.Injective ρ.action)
    (hcoordinate : ∀ c : G.Coordinates,
      ∃ q : Variety.PolynomialFunction (tVariety k (Module.finrank k V)),
        Variety.PolynomialFunction.pullback
          (triangularRepresentationMorphismOfBasis ρ hρ b htri).toVariety q =
          Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X c)) :
    let f := triangularRepresentationMorphismOfBasis ρ hρ b htri
    letI : AlgebraicGroup f.imageClosedSubgroup.carrierVariety :=
      f.imageClosedSubgroup.carrierAlgebraicGroup
    ∃ e : AlgebraicGroup.Iso G f.imageClosedSubgroup.carrierVariety,
      e.hom = f.codRestrictClosedSubgroup f.imageClosedSubgroup
        (fun y => ⟨y, rfl⟩) := by
  let f := triangularRepresentationMorphismOfBasis ρ hρ b htri
  exact f.iso_imageClosedSubgroup_of_coordinate_preimage
    (triangularRepresentationMorphismOfBasis_injective ρ hρ b htri hinj)
    hcoordinate

end

end Theory.AlgebraicGroup

