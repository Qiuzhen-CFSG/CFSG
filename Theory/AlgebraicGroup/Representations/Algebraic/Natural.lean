module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.PluckerOrbit.Conjugation
public import Theory.AlgebraicGroup.RootSystems.Defs

universe u v

/-! Natural representations of linear and classical algebraic groups. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! Local classical-group interfaces used by the representation predicates.
These are kept here to avoid a dependency cycle through Section10. -/

public abbrev RepQuadraticIsometryPointGroup
    {V : Type v} [AddCommGroup V] [Module k V]
    (q : QuadraticForm k V) := q.IsometryEquiv q

public instance RepQuadraticIsometryPointGroup.instGroup
    {V : Type v} [AddCommGroup V] [Module k V]
    (q : QuadraticForm k V) : Group (RepQuadraticIsometryPointGroup q) where
  one := QuadraticMap.IsometryEquiv.refl q
  mul f g := g.trans f
  inv f := f.symm
  mul_assoc a b c := by apply DFunLike.coe_injective; funext x; rfl
  one_mul a := by apply DFunLike.coe_injective; funext x; rfl
  mul_one a := by apply DFunLike.coe_injective; funext x; rfl
  inv_mul_cancel a := by
    apply DFunLike.coe_injective
    funext x
    exact a.symm_apply_apply x

@[expose]
public def RepQuadraticIsometryToLinearEquiv
    {V : Type v} [AddCommGroup V] [Module k V]
    (q : QuadraticForm k V) :
    RepQuadraticIsometryPointGroup q →* (V ≃ₗ[k] V) where
  toFun g := g.toLinearEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose]
public noncomputable def RepSpecialQuadraticIsometryPointGroup
    {V : Type v} [AddCommGroup V] [Module k V]
    (q : QuadraticForm k V) : Subgroup (RepQuadraticIsometryPointGroup q) :=
  (LinearEquiv.det.comp (RepQuadraticIsometryToLinearEquiv q)).ker

public abbrev RepAlternatingIsometryPointGroup
    {V : Type v} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) := B.IsometryEquiv B

public instance RepAlternatingIsometryPointGroup.instGroup
    {V : Type v} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Group (RepAlternatingIsometryPointGroup B) where
  one := LinearMap.BilinForm.IsometryEquiv.refl B
  mul f g := g.trans f
  inv f := f.symm
  mul_assoc a b c := by apply DFunLike.coe_injective; funext x; rfl
  one_mul a := by apply DFunLike.coe_injective; funext x; rfl
  mul_one a := by apply DFunLike.coe_injective; funext x; rfl
  inv_mul_cancel a := by
    apply DFunLike.coe_injective
    funext x
    exact a.toLinearEquiv.symm_apply_apply x

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The standard point equivalence for `GLₙ`, with its multiplicative
structure made explicit. -/
@[expose]
public noncomputable def generalLinearPointMulEquiv (n : ℕ) :
    Variety.Point (glVariety n : Variety k) ≃* GL (Fin n) k where
  toEquiv := glPointEquiv n
  map_mul' x y := by
    change glPointEquiv n ((glPointEquiv n).symm
      (glPointEquiv n x * glPointEquiv n y)) = _
    simp

/-- The natural action obtained from an algebraic identification with a closed
linear subgroup. -/
@[expose]
public noncomputable def naturalClosedLinearSubgroupRepresentation
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (H : ClosedSubgroup (glVarietyOf k V))
    (hKH : AlgebraicGroup.Iso K H.carrierVariety) :
    RationalRepresentation K V where
  action :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp
        ((generalLinearPointMulEquiv (k := k) (Module.finrank k V)).toMonoidHom.comp
          (H.inclusion.onPoints.comp hKH.hom.onPoints)))

/-- Pointwise specification of the natural action of a closed linear
subgroup. -/
@[expose]
public def IsNaturalClosedLinearSubgroupRepresentation
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (H : ClosedSubgroup (glVarietyOf k V))
    (hKH : AlgebraicGroup.Iso K H.carrierVariety)
    (ρ : RationalRepresentation K V) : Prop :=
  ∀ g, ρ.action g =
    glPointEquivOf k V e (H.inclusion.onPoints (hKH.hom.onPoints g))

/-- The natural action of a closed linear subgroup is rational. -/
public theorem naturalClosedLinearSubgroupRepresentation_isRational
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (H : ClosedSubgroup (glVarietyOf k V))
    (hKH : AlgebraicGroup.Iso K H.carrierVariety) :
    IsRationalRepresentation
      (naturalClosedLinearSubgroupRepresentation e H hKH) := by
  refine ⟨e, H.inclusion.comp hKH.hom, ?_⟩
  intro g
  apply Units.ext
  rfl

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The regular inclusion of the standard special linear group into the
general linear group. -/
@[expose]
public noncomputable def specialLinearToGeneralLinearMorphism (n : ℕ) :
    AlgebraicGroup.Morphism (slVariety k n) (glVariety n : Variety k) where
  toVariety := {
    toFun := fun x => (glPointEquiv n).symm
      (Matrix.SpecialLinearGroup.toGL (slPointEquiv n x))
    regular := by
      intro c
      rcases c with ⟨i, j⟩ | ⟨q⟩
      · refine ⟨MvPolynomial.X (ULift.up (i, j)), ?_⟩
        intro x
        simp [evalPolynomial]
        rfl
      · refine ⟨1, ?_⟩
        intro x
        change ((glPointEquiv n).symm
          (Matrix.SpecialLinearGroup.toGL (slPointEquiv n x))).val
            (Sum.inr PUnit.unit) = _
        change ((slPointEquiv n x).1.det)⁻¹ = _
        rw [(slPointEquiv n x).2]
        simp [evalPolynomial] }
  map_one := by
    apply (glPointEquiv n).injective
    rfl
  map_mul := by
    intro x y
    apply (glPointEquiv n).injective
    rfl

/-- The standard point equivalence for `SLₙ`, with its multiplicative
structure made explicit. -/
@[expose]
public def specialLinearPointMulEquiv (n : ℕ) :
    Variety.Point (slVariety k n) ≃*
      Matrix.SpecialLinearGroup (Fin n) k where
  toEquiv := slPointEquiv n
  map_mul' _ _ := rfl

/-- The natural linear action obtained from an identification with `SL(V)`. -/
@[expose]
public noncomputable def naturalSLRepresentation
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hKSL : AlgebraicGroup.Iso K (slVarietyOf k V))
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    RationalRepresentation K V where
  action :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp
        (Matrix.SpecialLinearGroup.toGL.comp
          ((specialLinearPointMulEquiv (k := k) (Module.finrank k V)).toMonoidHom.comp
            hKSL.hom.onPoints)))

/-- The natural action transported along an identification `K ≅ SL(V)`. -/
@[expose]
public def IsNaturalSLRepresentation
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hKSL : AlgebraicGroup.Iso K (slVarietyOf k V))
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (ρ : RationalRepresentation K V) : Prop :=
  ∀ g, ρ.action g = (slToFunOf k V e (hKSL.hom.onPoints g)).1

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def IsClassicalDynkinType (classification : RootClassification) : Prop :=
  classification.kind = .A ∨ classification.kind = .B ∨
    classification.kind = .C ∨ classification.kind = .D

@[expose]
public def classicalNaturalDimension (classification : RootClassification) : ℕ :=
  match classification.kind with
  | .A => classification.rank + 1
  | .B => 2 * classification.rank + 1
  | .C | .D => 2 * classification.rank
  | .E6 | .E7 | .E8 | .F4 | .G2 => 0

/-- A concrete classical natural linear model.  The point-group equivalence is
required to agree with the actual inclusion into `GL(V)`, so this predicate
does not merely attach an unrelated classical-group label to a representation.
For types `B` and `D`, `φ` is the Spin-to-orthogonal isogeny. -/
@[expose]
public def IsClassicalNaturalLinearModel
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (classification : RootClassification)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (H : ClosedSubgroup (glVarietyOf k V))
    (φ : AlgebraicGroup.Morphism K H.carrierVariety) : Prop :=
  IsIsogeny φ ∧
    match classification.kind with
    | .A =>
        Module.finrank k V = classification.rank + 1 ∧
          ∃ hHSL : Variety.Point H.carrierVariety ≃*
              Matrix.SpecialLinearGroup (Fin (Module.finrank k V)) k,
            ∀ h, glPointEquivOf k V e (H.inclusion.onPoints h) =
              LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm
                (Matrix.GeneralLinearGroup.toLin
                  (Matrix.SpecialLinearGroup.toGL (hHSL h)))
    | .B =>
        Module.finrank k V = 2 * classification.rank + 1 ∧
          ∃ q : QuadraticForm k V, q.Nondegenerate ∧
            ∃ hHOrth : Variety.Point H.carrierVariety ≃*
                RepSpecialQuadraticIsometryPointGroup q,
              ∀ h,
                LinearMap.GeneralLinearGroup.generalLinearEquiv k V
                    (glPointEquivOf k V e (H.inclusion.onPoints h)) =
                  (hHOrth h).1.toLinearEquiv
    | .C =>
        Module.finrank k V = 2 * classification.rank ∧
          ∃ ω : LinearMap.BilinForm k V, LinearMap.IsAlt ω ∧ ω.Nondegenerate ∧
            ∃ hHSp : Variety.Point H.carrierVariety ≃*
                RepAlternatingIsometryPointGroup ω,
              ∀ h,
                LinearMap.GeneralLinearGroup.generalLinearEquiv k V
                    (glPointEquivOf k V e (H.inclusion.onPoints h)) =
                  (hHSp h).toLinearEquiv
    | .D =>
        Module.finrank k V = 2 * classification.rank ∧
          ∃ q : QuadraticForm k V, q.Nondegenerate ∧
            ∃ hHOrth : Variety.Point H.carrierVariety ≃*
                RepSpecialQuadraticIsometryPointGroup q,
              ∀ h,
                LinearMap.GeneralLinearGroup.generalLinearEquiv k V
                    (glPointEquivOf k V e (H.inclusion.onPoints h)) =
                  (hHOrth h).1.toLinearEquiv
    | .E6 | .E7 | .E8 | .F4 | .G2 => False

/-- The natural action obtained by mapping an algebraic group into a concrete
closed linear model.  This covers both direct classical identifications and
the Spin-to-orthogonal morphisms used in types `B` and `D`. -/
@[expose]
public noncomputable def naturalClosedLinearSubgroupRepresentationAlong
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (H : ClosedSubgroup (glVarietyOf k V))
    (φ : AlgebraicGroup.Morphism K H.carrierVariety) :
    RationalRepresentation K V where
  action :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp
        ((generalLinearPointMulEquiv (k := k) (Module.finrank k V)).toMonoidHom.comp
          (H.inclusion.onPoints.comp φ.onPoints)))

@[expose]
public def IsNaturalClosedLinearSubgroupRepresentationAlong
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (H : ClosedSubgroup (glVarietyOf k V))
    (φ : AlgebraicGroup.Morphism K H.carrierVariety)
    (ρ : RationalRepresentation K V) : Prop :=
  ∀ g, ρ.action g =
    glPointEquivOf k V e (H.inclusion.onPoints (φ.onPoints g))

/-- The natural action along a morphism to a closed linear model is rational. -/
public theorem naturalClosedLinearSubgroupRepresentationAlong_isRational
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (H : ClosedSubgroup (glVarietyOf k V))
    (φ : AlgebraicGroup.Morphism K H.carrierVariety) :
    IsRationalRepresentation
      (naturalClosedLinearSubgroupRepresentationAlong e H φ) := by
  refine ⟨e, H.inclusion.comp φ, ?_⟩
  intro g
  apply Units.ext
  rfl

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def generalLinearConjugationRationalRepresentation (n : ℕ) :
    RationalRepresentation (glVariety n : Variety k) (Module.End k (Fin n → k)) :=
  ⟨generalLinearConjugationPointRepresentation (k := k) n⟩

public theorem generalLinearConjugationRationalRepresentation_isRational (n : ℕ) :
    IsRationalRepresentation
      (generalLinearConjugationRationalRepresentation (k := k) n) := by
  let b := generalLinearConjugationEndBasis (generalLinearStandardBasis (k := k) n)
  refine ⟨b, generalLinearConjugationMorphism (k := k) n, ?_⟩
  intro x
  change glPointEquivOf k (Module.End k (Fin n → k)) b
    (generalLinearRepresentationPoint b
      (generalLinearConjugationPointRepresentation (k := k) n x)) =
    generalLinearConjugationPointRepresentation (k := k) n x
  exact glPointEquivOf_generalLinearRepresentationPoint b
    (generalLinearConjugationPointRepresentation (k := k) n x)

end

end Theory.AlgebraicGroup
