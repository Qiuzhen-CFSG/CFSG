module

public import Theory.AlgebraicGroup.Representations.Matrix
public import Theory.AlgebraicGroup.Tori.Character.Image

universe u v

/-! The diagonal torus in a general linear group determined by a finite
basis. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]

noncomputable def basisDiagonalLinearEquiv
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (a : Fin (Module.finrank k V) → kˣ) : V ≃ₗ[k] V :=
  b.equivFun |>.trans
    (LinearEquiv.piCongrRight fun i ↦ (a i).mulLeftLinearEquiv k k) |>.trans
      b.equivFun.symm

omit [IsAlgClosed k] [Module.Finite k V] in
lemma basisDiagonalLinearEquiv_apply_basis
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (a : Fin (Module.finrank k V) → kˣ)
    (i : Fin (Module.finrank k V)) :
    basisDiagonalLinearEquiv b a (b i) = (a i : k) • b i := by
  have hb : b.equivFun (b i) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  change b.equivFun.symm
      ((LinearEquiv.piCongrRight fun i ↦
        (a i).mulLeftLinearEquiv k k) (b.equivFun (b i))) = _
  rw [hb]
  have hscaled :
      (LinearEquiv.piCongrRight fun i ↦
          (a i).mulLeftLinearEquiv k k) (Pi.single i 1) =
        (a i : k) • Pi.single i 1 := by
    funext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Ne.symm hij]
  rw [hscaled, map_smul, ← hb, b.equivFun.symm_apply_apply]

noncomputable def basisDiagonalGeneralLinear
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (a : Fin (Module.finrank k V) → kˣ) :
    LinearMap.GeneralLinearGroup k V :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (basisDiagonalLinearEquiv b a)

omit [IsAlgClosed k] [Module.Finite k V] in
lemma basisDiagonalGeneralLinear_apply_basis
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (a : Fin (Module.finrank k V) → kˣ)
    (i : Fin (Module.finrank k V)) :
    ((basisDiagonalGeneralLinear b a : LinearMap.GeneralLinearGroup k V) :
      Module.End k V) (b i) = (a i : k) • b i := by
  exact basisDiagonalLinearEquiv_apply_basis b a i

noncomputable def basisDiagonalRepresentation
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Variety.Point (dVariety k (Module.finrank k V)) →*
      LinearMap.GeneralLinearGroup k V where
  toFun := fun x ↦ basisDiagonalGeneralLinear b
    (dPointEquiv (Module.finrank k V) x)
  map_one' := by
    apply Units.ext
    apply b.ext
    intro i
    simp [basisDiagonalGeneralLinear_apply_basis, dPointEquiv_one]
  map_mul' := by
    intro x y
    apply Units.ext
    apply b.ext
    intro i
    simp [basisDiagonalGeneralLinear_apply_basis, dPointEquiv_mul,
      smul_smul, mul_comm]

omit [IsAlgClosed k] [Module.Finite k V] in
lemma basisDiagonalRepresentation_apply_basis
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (dVariety k (Module.finrank k V)))
    (i : Fin (Module.finrank k V)) :
    ((basisDiagonalRepresentation b x : LinearMap.GeneralLinearGroup k V) :
      Module.End k V) (b i) =
        dPointEntry (Module.finrank k V) x i • b i := by
  exact basisDiagonalGeneralLinear_apply_basis b
    (dPointEquiv (Module.finrank k V) x) i

noncomputable def basisDiagonalMatrixCoefficient
    (i j : Fin (Module.finrank k V)) :
    (dVariety k (Module.finrank k V)).PolynomialFunction :=
  if i = j then
    Variety.PolynomialFunction.ofPolynomial _
      (MvPolynomial.X (Sum.inl (ULift.up j)))
  else 0

omit [IsAlgClosed k] [Module.Finite k V] in
lemma basisDiagonalMatrixCoefficient_apply
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (i j : Fin (Module.finrank k V))
    (x : Variety.Point (dVariety k (Module.finrank k V))) :
    basisDiagonalMatrixCoefficient (V := V) i j x =
      b.repr (((basisDiagonalRepresentation b x :
        LinearMap.GeneralLinearGroup k V) : Module.End k V) (b j)) i := by
  rw [basisDiagonalRepresentation_apply_basis]
  by_cases hij : i = j
  · subst i
    simp [basisDiagonalMatrixCoefficient,
      Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial, dPointEntry]
  · simp [basisDiagonalMatrixCoefficient, hij]

noncomputable def basisDiagonalInverseMatrixCoefficient
    (i j : Fin (Module.finrank k V)) :
    (dVariety k (Module.finrank k V)).PolynomialFunction :=
  Variety.PolynomialFunction.pullback
    (AlgebraicGroup.invMorphism (dVariety k (Module.finrank k V)))
    (basisDiagonalMatrixCoefficient (V := V) i j)

omit [IsAlgClosed k] [Module.Finite k V] in
lemma basisDiagonalInverseMatrixCoefficient_apply
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (i j : Fin (Module.finrank k V))
    (x : Variety.Point (dVariety k (Module.finrank k V))) :
    basisDiagonalInverseMatrixCoefficient (V := V) i j x =
      b.repr (((((basisDiagonalRepresentation b x)⁻¹ :
        LinearMap.GeneralLinearGroup k V) : Module.End k V)) (b j)) i := by
  change basisDiagonalMatrixCoefficient (V := V) i j x⁻¹ = _
  rw [basisDiagonalMatrixCoefficient_apply (b := b)]
  simp

noncomputable def basisDiagonalMorphism
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    AlgebraicGroup.Morphism (dVariety k (Module.finrank k V))
      (glVarietyOf k V) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b (basisDiagonalRepresentation b)
    (basisDiagonalMatrixCoefficient (V := V))
    (basisDiagonalInverseMatrixCoefficient (V := V))
    (basisDiagonalMatrixCoefficient_apply b)
    (basisDiagonalInverseMatrixCoefficient_apply b)

omit [Module.Finite k V] in
lemma basisDiagonalMorphism_apply
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (dVariety k (Module.finrank k V))) :
    (basisDiagonalMorphism b).onPoints x =
      generalLinearRepresentationPoint b (basisDiagonalRepresentation b x) :=
  rfl

lemma basisDiagonalMorphism_action_basis
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (dVariety k (Module.finrank k V)))
    (i : Fin (Module.finrank k V)) :
    ((glPointEquivOf k V b ((basisDiagonalMorphism b).onPoints x) :
      LinearMap.GeneralLinearGroup k V) : Module.End k V) (b i) =
        dPointEntry (Module.finrank k V) x i • b i := by
  rw [basisDiagonalMorphism_apply,
    glPointEquivOf_generalLinearRepresentationPoint]
  exact basisDiagonalRepresentation_apply_basis b x i

/-- A finite basis determines a regular diagonal-torus morphism into `GL(V)`.
Its canonical closed image is a subtorus, and its coordinates act on the
basis vectors by the corresponding scalars. -/
public theorem exists_basisDiagonalMorphism
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ∃ f : AlgebraicGroup.Morphism (dVariety k (Module.finrank k V))
        (glVarietyOf k V),
      IsSubtorus f.imageClosedSubgroup ∧
        ∀ x i,
          ((glPointEquivOf k V b (f.onPoints x) :
            LinearMap.GeneralLinearGroup k V) : Module.End k V) (b i) =
              dPointEntry (Module.finrank k V) x i • b i := by
  refine ⟨basisDiagonalMorphism b, ?_, basisDiagonalMorphism_action_basis b⟩
  exact morphism_image_isTorus (basisDiagonalMorphism b)
    (dVariety_isTorus (Module.finrank k V))

end Theory.AlgebraicGroup
