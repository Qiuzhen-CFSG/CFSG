module

public import Theory.AlgebraicGroup.PluckerOrbit.Basic

universe u

/-! Regular matrix coefficients of the restricted Plücker orbit-span representation. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan)) :
    G.PolynomialFunction :=
  H.rightTranslateVanishingExteriorLinearMatrixCoefficient
    (H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension i)
    (H.rightTranslateVanishingPluckerOrbitSpanBasis j)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan))
    (g : Variety.Point G) :
    H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient i j g =
      H.rightTranslateVanishingPluckerOrbitSpanBasis.repr
        (((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
          LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
          Module.End k H.rightTranslateVanishingPluckerOrbitSpan)
          (H.rightTranslateVanishingPluckerOrbitSpanBasis j)) i := by
  calc
    H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient i j g =
        H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension i
          (((H.rightTranslateVanishingExteriorGeneralLinear g :
            LinearMap.GeneralLinearGroup k _) : Module.End k _)
            (H.rightTranslateVanishingPluckerOrbitSpanBasis j)) := by
      simpa [ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient] using
        H.rightTranslateVanishingExteriorLinearMatrixCoefficient_apply
          (H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension i)
          (H.rightTranslateVanishingPluckerOrbitSpanBasis j) g
    _ = H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension i
          (((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
            LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
            Module.End k H.rightTranslateVanishingPluckerOrbitSpan)
            (H.rightTranslateVanishingPluckerOrbitSpanBasis j) : _) :=
      (H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension_restricted_eq_ambient
        i g (H.rightTranslateVanishingPluckerOrbitSpanBasis j)).symm
    _ = _ :=
      H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension_restricted_apply
        i g (H.rightTranslateVanishingPluckerOrbitSpanBasis j)

end

/-! Inverse matrix coefficients of the restricted Plücker orbit-span representation. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan)) :
    G.PolynomialFunction :=
  Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
    (H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient i j)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan))
    (g : Variety.Point G) :
    H.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient i j g =
      H.rightTranslateVanishingPluckerOrbitSpanBasis.repr
        (((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g⁻¹ :
          LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
          Module.End k H.rightTranslateVanishingPluckerOrbitSpan)
          (H.rightTranslateVanishingPluckerOrbitSpanBasis j)) i := by
  exact H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient_apply i j g⁻¹

end

/-! The restricted Plücker orbit-span representation matrix. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    Matrix (Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan))
      (Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan)) k :=
  LinearMap.toMatrix H.rightTranslateVanishingPluckerOrbitSpanBasis
    H.rightTranslateVanishingPluckerOrbitSpanBasis
    ((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
      LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
      Module.End k H.rightTranslateVanishingPluckerOrbitSpan)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G)
    (i j : Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan)) :
    H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix g i j =
      H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient i j g := by
  rw [ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix,
    LinearMap.toMatrix_apply]
  exact (H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient_apply i j g).symm

end

/-! Inverse matrix coefficients are entries of the inverse representation matrix. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient_eq_representationMatrix
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan))
    (g : Variety.Point G) :
    H.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient i j g =
      H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix g⁻¹ i j := by
  change H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient i j g⁻¹ = _
  exact (H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix_apply g⁻¹ i j).symm

end

/-! Determinant of the inverse restricted Plücker representation matrix. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix_inv_det
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    (H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix g⁻¹).det =
      (H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix g).det⁻¹ := by
  let W : Type u := H.rightTranslateVanishingPluckerOrbitSpan
  let ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k W :=
    H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear
  let b : Module.Basis (Fin (Module.finrank k W)) k W :=
    H.rightTranslateVanishingPluckerOrbitSpanBasis
  have hinv : ρ g⁻¹ = (ρ g)⁻¹ := map_inv ρ g
  have hmatrix := congrArg
    (fun x : LinearMap.GeneralLinearGroup k W =>
      (LinearMap.toMatrix b b (x : Module.End k W)).det) hinv
  have hdet := generalLinear_toMatrix_inv_det (k := k) (V := W)
    (ι := Fin (Module.finrank k W)) b (ρ g)
  calc
    (H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix g⁻¹).det =
        (LinearMap.toMatrix b b ((ρ g⁻¹ :
          LinearMap.GeneralLinearGroup k W) : Module.End k W)).det := rfl
    _ = (LinearMap.toMatrix b b (((ρ g)⁻¹ :
          LinearMap.GeneralLinearGroup k W) : Module.End k W)).det := hmatrix
    _ = (LinearMap.toMatrix b b ((ρ g :
          LinearMap.GeneralLinearGroup k W) : Module.End k W)).det⁻¹ := hdet
    _ = (H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix g).det⁻¹ := rfl

end

/-! The inverse determinant coordinate of the restricted Plücker representation. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanInverseDeterminant
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    G.PolynomialFunction :=
  Matrix.det (fun i j =>
    H.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient i j)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanInverseDeterminant_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.rightTranslateVanishingPluckerOrbitSpanInverseDeterminant g =
      (H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix g).det⁻¹ := by
  let ev : G.PolynomialFunction →+* k :=
    { toFun := fun f => f g
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let M : Matrix
      (Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan))
      (Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan))
      G.PolynomialFunction := fun i j =>
    H.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient i j
  have hEval : H.rightTranslateVanishingPluckerOrbitSpanInverseDeterminant g =
      (H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix g⁻¹).det := by
    change ev (Matrix.det M) = _
    rw [RingHom.map_det]
    congr 1
    funext i j
    change H.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient i j g = _
    exact H.rightTranslateVanishingPluckerOrbitSpanInverseMatrixCoefficient_eq_representationMatrix
      i j g
  rw [hEval]
  exact H.rightTranslateVanishingPluckerOrbitSpanRepresentationMatrix_inv_det g

end

/-! Regularity of the restricted Plücker orbit-span representation. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    AlgebraicGroup.Morphism G
      (glVariety (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan) : Variety k) :=
  generalLinearRepresentationMorphism
    (V := H.rightTranslateVanishingPluckerOrbitSpan)
    H.rightTranslateVanishingPluckerOrbitSpanBasis
    H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear
    H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient
    (fun i j g => H.rightTranslateVanishingPluckerOrbitSpanMatrixCoefficient_apply i j g)
    H.rightTranslateVanishingPluckerOrbitSpanInverseDeterminant
    (fun g => H.rightTranslateVanishingPluckerOrbitSpanInverseDeterminant_apply g)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism.onPoints g =
      generalLinearRepresentationPoint (k := k)
        (V := H.rightTranslateVanishingPluckerOrbitSpan)
        H.rightTranslateVanishingPluckerOrbitSpanBasis
        (H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g) :=
  rfl

end

end Theory.AlgebraicGroup
