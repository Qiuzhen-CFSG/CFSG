module

public import Theory.AlgebraicGroup.Representations.Exterior
public import Theory.AlgebraicGroup.Representations.Matrix
public import Theory.AlgebraicGroup.RightTranslation.MatrixCoefficients

universe u v

/-!
The closed-subgroup right-translation representation as a regular algebraic-group morphism.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A matrix coefficient of the inverse coordinate-translation
representation, obtained by pullback along group inversion. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingInverseMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Module.finrank k (H.rightTranslateVanishingSpan))) :
    Variety.PolynomialFunction G :=
  Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
    (H.rightTranslateVanishingMatrixCoefficient
      (H.rightTranslateVanishingSpanBasis) i j)

/-- The determinant of the inverse representation matrix.  This is the
regular function used for the extra determinant-inverse coordinate of
`GL(V)`. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingInverseDeterminant
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.PolynomialFunction G :=
  Matrix.det (fun i j =>
    H.rightTranslateVanishingInverseMatrixCoefficient i j)

omit [IsAlgClosed k] in
/-- Evaluation of the inverse-determinant function is the inverse determinant
of the coordinate-translation representation matrix. -/
public lemma ClosedSubgroup.rightTranslateVanishingInverseDeterminant_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) (g : Variety.Point G) :
    H.rightTranslateVanishingInverseDeterminant g =
      (LinearMap.toMatrix (H.rightTranslateVanishingSpanBasis)
        (H.rightTranslateVanishingSpanBasis)
        ((H.rightTranslateVanishingSpanGeneralLinear g :
          LinearMap.GeneralLinearGroup k
            (H.rightTranslateVanishingSpan)) :
          Module.End k (H.rightTranslateVanishingSpan))).det⁻¹ := by
  let ev : Variety.PolynomialFunction G →+* k :=
    { toFun := fun f => f g
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let B : Matrix
      (Fin (Module.finrank k (H.rightTranslateVanishingSpan)))
      (Fin (Module.finrank k (H.rightTranslateVanishingSpan))) k :=
    LinearMap.toMatrix (H.rightTranslateVanishingSpanBasis)
      (H.rightTranslateVanishingSpanBasis)
      ((H.rightTranslateVanishingSpanGeneralLinear g⁻¹ :
        LinearMap.GeneralLinearGroup k
          (H.rightTranslateVanishingSpan)) :
        Module.End k (H.rightTranslateVanishingSpan))
  let A : Matrix
      (Fin (Module.finrank k (H.rightTranslateVanishingSpan)))
      (Fin (Module.finrank k (H.rightTranslateVanishingSpan))) k :=
    LinearMap.toMatrix (H.rightTranslateVanishingSpanBasis)
      (H.rightTranslateVanishingSpanBasis)
      ((H.rightTranslateVanishingSpanGeneralLinear g :
        LinearMap.GeneralLinearGroup k
          (H.rightTranslateVanishingSpan)) :
        Module.End k (H.rightTranslateVanishingSpan))
  let invM : Matrix
      (Fin (Module.finrank k (H.rightTranslateVanishingSpan)))
      (Fin (Module.finrank k (H.rightTranslateVanishingSpan)))
      G.PolynomialFunction := fun i j => H.rightTranslateVanishingInverseMatrixCoefficient i j
  have hEval : H.rightTranslateVanishingInverseDeterminant g = B.det := by
    change ev (Matrix.det invM) = B.det
    rw [RingHom.map_det]
    congr 1
    funext i j
    change H.rightTranslateVanishingMatrixCoefficient
        (H.rightTranslateVanishingSpanBasis) i j g⁻¹ = B i j
    rw [H.rightTranslateVanishingMatrixCoefficient_apply]
    change _ = (LinearMap.toMatrix (H.rightTranslateVanishingSpanBasis)
      (H.rightTranslateVanishingSpanBasis)
      ((H.rightTranslateVanishingSpanGeneralLinear g⁻¹ :
        LinearMap.GeneralLinearGroup k
          (H.rightTranslateVanishingSpan)) :
        Module.End k (H.rightTranslateVanishingSpan))) i j
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [hEval]
  change B.det = A.det⁻¹
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix_mul]
    have hlin :
        (↑(H.rightTranslateVanishingSpanGeneralLinear g⁻¹) :
          Module.End k H.rightTranslateVanishingSpan) *
            ↑(H.rightTranslateVanishingSpanGeneralLinear g) = 1 := by
      rw [← Units.val_mul]
      exact congrArg
        (fun z : LinearMap.GeneralLinearGroup k H.rightTranslateVanishingSpan =>
          (z : Module.End k H.rightTranslateVanishingSpan))
        (show H.rightTranslateVanishingSpanGeneralLinear g⁻¹ *
            H.rightTranslateVanishingSpanGeneralLinear g = 1 by simp)
    rw [hlin]
    exact LinearMap.toMatrix_one _
  apply eq_inv_of_mul_eq_one_left
  rw [← Matrix.det_mul, hBA, Matrix.det_one]

public noncomputable def ClosedSubgroup.rightTranslateVanishingPointMulEquiv
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.Point (glVarietyOf k (H.rightTranslateVanishingSpan)) ≃*
      LinearMap.GeneralLinearGroup k (H.rightTranslateVanishingSpan) :=
  (translationGLPointMulEquiv
    (Module.finrank k (H.rightTranslateVanishingSpan))).trans
      (Matrix.GeneralLinearGroup.toLin' (H.rightTranslateVanishingSpanBasis))

/-- The point map underlying the regular coordinate-translation
representation. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingRepresentationPoint
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) (g : Variety.Point G) :
    Variety.Point (glVarietyOf k (H.rightTranslateVanishingSpan)) :=
  (H.rightTranslateVanishingPointMulEquiv).symm
    (H.rightTranslateVanishingSpanGeneralLinear g)

/-- The matrix coordinates of the transported representation point are the
regular matrix-coefficient functions constructed above. -/
public lemma ClosedSubgroup.rightTranslateVanishingRepresentationPoint_matrix
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G)
    (i j : Fin (Module.finrank k (H.rightTranslateVanishingSpan))) :
    (H.rightTranslateVanishingRepresentationPoint g).val (Sum.inl (i, j)) =
      H.rightTranslateVanishingMatrixCoefficient
        (H.rightTranslateVanishingSpanBasis) i j g := by
  change glMatrixOfPoint (Module.finrank k
      (H.rightTranslateVanishingSpan))
    ((glPointEquivOf k (H.rightTranslateVanishingSpan)
      (H.rightTranslateVanishingSpanBasis)).symm
        (H.rightTranslateVanishingSpanGeneralLinear g)) i j = _
  change (LinearMap.toMatrix (H.rightTranslateVanishingSpanBasis)
    (H.rightTranslateVanishingSpanBasis)
    ((H.rightTranslateVanishingSpanGeneralLinear g :
      LinearMap.GeneralLinearGroup k
        (H.rightTranslateVanishingSpan)) :
      Module.End k (H.rightTranslateVanishingSpan))) i j = _
  rw [LinearMap.toMatrix_apply,
    H.rightTranslateVanishingMatrixCoefficient_apply]
  rfl

/-- The scalar coordinate of the transported representation point is the
regular inverse-determinant function. -/
public lemma ClosedSubgroup.rightTranslateVanishingRepresentationPoint_scalar
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) (g : Variety.Point G) :
    (H.rightTranslateVanishingRepresentationPoint g).val
        (Sum.inr PUnit.unit) =
      H.rightTranslateVanishingInverseDeterminant g := by
  change glScalarOfPoint (Module.finrank k
      (H.rightTranslateVanishingSpan))
    ((glPointEquivOf k (H.rightTranslateVanishingSpan)
      (H.rightTranslateVanishingSpanBasis)).symm
        (H.rightTranslateVanishingSpanGeneralLinear g)) = _
  have hdet := glScalarOfPoint_eq_inv_det
    (Module.finrank k H.rightTranslateVanishingSpan)
    ((glPointEquivOf k (H.rightTranslateVanishingSpan)
      (H.rightTranslateVanishingSpanBasis)).symm
      (H.rightTranslateVanishingSpanGeneralLinear g))
  rw [show glScalarOfPoint (Module.finrank k
      (H.rightTranslateVanishingSpan))
      ((glPointEquivOf k (H.rightTranslateVanishingSpan)
        (H.rightTranslateVanishingSpanBasis)).symm
        (H.rightTranslateVanishingSpanGeneralLinear g)) = _ by
      simpa [glVarietyOf] using hdet]
  rw [H.rightTranslateVanishingInverseDeterminant_apply]
  congr 1

/-- The faithful coordinate-translation representation is regular. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingRepresentationMorphism
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    AlgebraicGroup.Morphism G
      (glVarietyOf k (H.rightTranslateVanishingSpan)) where
  toVariety :=
    { toFun := H.rightTranslateVanishingRepresentationPoint
      regular := by
        intro c
        cases c with
        | inl ij =>
            rcases ij with ⟨i, j⟩
            rcases (H.rightTranslateVanishingMatrixCoefficient
              (H.rightTranslateVanishingSpanBasis) i j).representedBy with ⟨p, hp⟩
            refine ⟨p, fun g => ?_⟩
            rw [← hp g]
            exact H.rightTranslateVanishingRepresentationPoint_matrix g i j
        | inr q =>
            cases q
            rcases (H.rightTranslateVanishingInverseDeterminant).representedBy with
              ⟨p, hp⟩
            refine ⟨p, fun g => ?_⟩
            rw [← hp g]
            exact H.rightTranslateVanishingRepresentationPoint_scalar g }
  map_one := by
    simp [rightTranslateVanishingRepresentationPoint]
  map_mul := by
    intro g h
    simp [rightTranslateVanishingRepresentationPoint]

/-- On rational points, the regular morphism is the original transported
coordinate-translation representation. -/
public lemma ClosedSubgroup.rightTranslateVanishingRepresentationMorphism_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) (g : Variety.Point G) :
    (H.rightTranslateVanishingRepresentationMorphism).onPoints g =
      H.rightTranslateVanishingRepresentationPoint g :=
  rfl

/-- The regular Chevalley representation rebuilt in an arbitrary basis. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingRepresentationMorphismOfBasis
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (e : Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan) :
    AlgebraicGroup.Morphism G
      (glVarietyOf k H.rightTranslateVanishingSpan) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient e
    H.rightTranslateVanishingSpanGeneralLinear
    (H.rightTranslateVanishingMatrixCoefficient e)
    (fun i j => Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
      (H.rightTranslateVanishingMatrixCoefficient e i j))
    (fun i j g => H.rightTranslateVanishingMatrixCoefficient_apply e i j g)
    (by
      intro i j g
      change H.rightTranslateVanishingMatrixCoefficient e i j g⁻¹ = _
      rw [H.rightTranslateVanishingMatrixCoefficient_apply]
      congr 2)

/-- The arbitrary-basis regular Chevalley morphism has the original linear
representation as its point action. -/
public lemma ClosedSubgroup.rightTranslateVanishingRepresentationMorphismOfBasis_pointEquiv
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (e : Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan) (g : Variety.Point G) :
    glPointEquivOf k H.rightTranslateVanishingSpan e
        ((H.rightTranslateVanishingRepresentationMorphismOfBasis e).onPoints g) =
      H.rightTranslateVanishingSpanGeneralLinear g := by
  change glPointEquivOf k H.rightTranslateVanishingSpan e
      (generalLinearRepresentationPoint e
        (H.rightTranslateVanishingSpanGeneralLinear g)) = _
  exact glPointEquivOf_generalLinearRepresentationPoint e
    (H.rightTranslateVanishingSpanGeneralLinear g)

/-- Every function in the finite Chevalley right-translation space is a
linear matrix coefficient of its regular representation. -/
public lemma ClosedSubgroup.rightTranslateVanishingSpan_eq_linearMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (e : Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan)
    (q : H.rightTranslateVanishingSpan) :
    q.1 = rationalRepresentationLinearMatrixCoefficient
      (⟨H.rightTranslateVanishingSpanGeneralLinear⟩ :
        RationalRepresentation G H.rightTranslateVanishingSpan)
      e (H.rightTranslateVanishingRepresentationMorphismOfBasis e)
      (polynomialFunctionSubspaceEvaluation G H.rightTranslateVanishingSpan 1) q := by
  apply Variety.PolynomialFunction.ext
  intro g
  rw [rationalRepresentationLinearMatrixCoefficient_apply]
  · change q.1 g = q.1 (1 * g)
    rw [one_mul]
  · exact H.rightTranslateVanishingRepresentationMorphismOfBasis_pointEquiv e

/-- Every finite Chevalley right-translation function lies in the pullback
range of the arbitrary-basis representation morphism. -/
public lemma ClosedSubgroup.rightTranslateVanishingSpan_mem_pullback_range
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (e : Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan)
    (q : H.rightTranslateVanishingSpan) :
    q.1 ∈ Set.range
      (H.rightTranslateVanishingRepresentationMorphismOfBasis e).toVariety.pullbackAlgHom := by
  rw [H.rightTranslateVanishingSpan_eq_linearMatrixCoefficient e q]
  let l := polynomialFunctionSubspaceEvaluation G H.rightTranslateVanishingSpan 1
  let n := Module.finrank k H.rightTranslateVanishingSpan
  let targetCoordinate (i j : Fin n) :
      (glVarietyOf k H.rightTranslateVanishingSpan).PolynomialFunction :=
    Variety.PolynomialFunction.ofPolynomial _ (MvPolynomial.X (Sum.inl (i, j)))
  let Q : (glVarietyOf k H.rightTranslateVanishingSpan).PolynomialFunction :=
    ∑ i, ∑ j,
      algebraMap k (glVarietyOf k H.rightTranslateVanishingSpan).PolynomialFunction (l (e i)) *
      algebraMap k (glVarietyOf k H.rightTranslateVanishingSpan).PolynomialFunction (e.repr q j) *
      targetCoordinate i j
  refine ⟨Q, ?_⟩
  unfold rationalRepresentationLinearMatrixCoefficient
  dsimp [Q, n, targetCoordinate]
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
  rw [rationalRepresentationMatrixCoefficient]
  rw [map_mul]
  rfl

/-- Every chosen vanishing-ideal generator lies in the pullback range of the
arbitrary-basis representation morphism. -/
public lemma ClosedSubgroup.vanishingIdealGenerator_mem_pullback_range
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (e : Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan)
    (i : H.vanishingIdealGeneratorData.generators) :
    i.1 ∈ Set.range
      (H.rightTranslateVanishingRepresentationMorphismOfBasis e).toVariety.pullbackAlgHom := by
  let q : H.rightTranslateVanishingSpan :=
    ⟨i.1, H.generator_mem_rightTranslateVanishingSpan i⟩
  exact H.rightTranslateVanishingSpan_mem_pullback_range e q

end

/-! The regular Chevalley representation has the prescribed subspace stabilizer. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A point belongs to `H` exactly when the regular finite-dimensional
right-translation representation preserves the distinguished subspace. -/
public lemma ClosedSubgroup.chevalleyRepresentation_stabilizer_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    (∀ q : H.rightTranslateVanishingSpan,
      q.1 ∈ H.rightTranslateVanishingSubspace →
      (((H.rightTranslateVanishingSpanGeneralLinear g :
        LinearMap.GeneralLinearGroup k H.rightTranslateVanishingSpan) :
          Module.End k H.rightTranslateVanishingSpan) q).1 ∈
        H.rightTranslateVanishingSubspace) ↔
      g ∈ H.toSubgroup := by
  change (∀ q : H.rightTranslateVanishingSpan,
    q.1 ∈ H.rightTranslateVanishingSubspace →
    (AlgebraicGroup.rightMulMorphism G g).pullbackAlgHom q.1 ∈
      H.rightTranslateVanishingSubspace) ↔ g ∈ H.toSubgroup
  constructor
  · intro hstable
    apply (H.rightTranslateVanishingSubspace_stabilizer_iff g).mp
    intro q hq
    exact hstable ⟨q, hq.1⟩ hq
  · intro hg q hq
    exact (H.rightTranslateVanishingSubspace_stabilizer_iff g).mpr hg q.1 hq

/-- The point map of the regular Chevalley morphism corresponds to the
underlying general-linear representation. -/
public lemma ClosedSubgroup.chevalleyRepresentationMorphism_pointEquiv
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.rightTranslateVanishingPointMulEquiv
      (H.rightTranslateVanishingRepresentationMorphism.onPoints g) =
        H.rightTranslateVanishingSpanGeneralLinear g := by
  rw [H.rightTranslateVanishingRepresentationMorphism_apply]
  exact H.rightTranslateVanishingPointMulEquiv.apply_symm_apply _

end

/-! The Plücker vector of the distinguished Chevalley subspace. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The distinguished vanishing subspace, regarded as a subspace of the
finite-dimensional Chevalley representation space. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingSubspaceInSpan
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Submodule k H.rightTranslateVanishingSpan :=
  H.rightTranslateVanishingSubspace.comap
    H.rightTranslateVanishingSpan.subtype

public noncomputable instance
    ClosedSubgroup.rightTranslateVanishingSubspaceInSpan_free
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Module.Free k H.rightTranslateVanishingSubspaceInSpan :=
  Module.Free.of_divisionRing k H.rightTranslateVanishingSubspaceInSpan

public noncomputable instance
    ClosedSubgroup.rightTranslateVanishingSubspaceInSpan_finite
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Module.Finite k H.rightTranslateVanishingSubspaceInSpan :=
  Module.Finite.of_injective
    H.rightTranslateVanishingSubspaceInSpan.subtype
    H.rightTranslateVanishingSubspaceInSpan.injective_subtype

/-- Abstract-degree top-wedge data for the distinguished subspace. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingTopWedgeData
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    FiniteSubspaceTopWedgeData k H.rightTranslateVanishingSubspaceInSpan where
  degree := Module.finrank k H.rightTranslateVanishingSubspaceInSpan
  basis := Module.finBasis k H.rightTranslateVanishingSubspaceInSpan

/-- The Plücker vector in the exterior power of the ambient Chevalley space. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerVector
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
      H.rightTranslateVanishingSpan :=
  exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
    H.rightTranslateVanishingSubspaceInSpan.subtype
    H.rightTranslateVanishingTopWedgeData.vector

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The distinguished-subspace top wedge is nonzero. -/
public lemma ClosedSubgroup.rightTranslateVanishingTopWedge_ne_zero
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.rightTranslateVanishingTopWedgeData.vector ≠ 0 :=
  H.rightTranslateVanishingTopWedgeData.vector_ne_zero

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The Plücker vector is nonzero. -/
public lemma ClosedSubgroup.rightTranslateVanishingPluckerVector_ne_zero
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.rightTranslateVanishingPluckerVector ≠ 0 := by
  intro hzero
  apply H.rightTranslateVanishingTopWedge_ne_zero
  apply (exteriorPower.map_injective_field
    (n := H.rightTranslateVanishingTopWedgeData.degree)
    H.rightTranslateVanishingSubspaceInSpan.injective_subtype)
  simpa [ClosedSubgroup.rightTranslateVanishingPluckerVector] using hzero

end

/-! The Plücker-line stabilizer of the regular Chevalley representation is the given subgroup. -/

section
open scoped ExteriorAlgebra
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.chevalleyPluckerLine_stabilizer_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
        (LinearMap.GeneralLinearGroup.toLinearEquiv
          (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap
        H.rightTranslateVanishingPluckerVector ∈
      k ∙ H.rightTranslateVanishingPluckerVector ↔
        g ∈ H.toSubgroup := by
  rw [ClosedSubgroup.rightTranslateVanishingPluckerVector]
  rw [H.rightTranslateVanishingTopWedgeData.map_mem_span_iff_range_stable
    H.rightTranslateVanishingSubspaceInSpan.subtype
    H.rightTranslateVanishingSubspaceInSpan.injective_subtype]
  rw [← H.chevalleyRepresentation_stabilizer_iff g]
  constructor
  · intro hstable q hq
    have hu := hstable ⟨q, hq⟩
    obtain ⟨v, hv⟩ := hu
    change (((H.rightTranslateVanishingSpanGeneralLinear g :
      LinearMap.GeneralLinearGroup k H.rightTranslateVanishingSpan) :
        Module.End k H.rightTranslateVanishingSpan) q).1 ∈
          H.rightTranslateVanishingSubspace
    have hv' : v.1 =
        ((H.rightTranslateVanishingSpanGeneralLinear g :
          LinearMap.GeneralLinearGroup k H.rightTranslateVanishingSpan) :
            Module.End k H.rightTranslateVanishingSpan) q := hv
    rw [← hv']
    exact v.2
  · intro hstable u
    have hu := hstable u.1 u.2
    let v : H.rightTranslateVanishingSubspaceInSpan :=
      ⟨((H.rightTranslateVanishingSpanGeneralLinear g :
        LinearMap.GeneralLinearGroup k H.rightTranslateVanishingSpan) :
          Module.End k H.rightTranslateVanishingSpan) u.1, hu⟩
    refine ⟨v, ?_⟩
    rfl

end
end Theory.AlgebraicGroup
