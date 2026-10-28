module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Theory.AlgebraicGroup.Representations.Matrix

universe u v w

/-! Standard operations on finite-dimensional rational representations. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

@[expose]
public def Intertwines
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation G V) (σ : RationalRepresentation G W)
    (f : V →ₗ[k] W) : Prop :=
  ∀ g v, f ((ρ.action g : Module.End k V) v) =
    (σ.action g : Module.End k W) (f v)

@[expose]
public def IsRestrictionRepresentation
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation G V) (W : Submodule k V)
    (σ : RationalRepresentation G W) : Prop :=
  Intertwines σ ρ W.subtype

@[expose]
public def IsQuotientRepresentation
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation G V) (W : Submodule k V)
    (σ : RationalRepresentation G (V ⧸ W)) : Prop :=
  ∀ g v, (σ.action g : Module.End k (V ⧸ W)) (Submodule.Quotient.mk v) =
    Submodule.Quotient.mk ((ρ.action g : Module.End k V) v)

@[expose]
public def IsDirectSumRepresentation
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation G V) (σ : RationalRepresentation G W)
    (τ : RationalRepresentation G (V × W)) : Prop :=
  ∀ g v w, (τ.action g : Module.End k (V × W)) (v, w) =
    ((ρ.action g : Module.End k V) v, (σ.action g : Module.End k W) w)

@[expose]
public def IsPullbackRepresentation
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    {V : Type v} [AddCommGroup V] [Module k V]
    (φ : AlgebraicGroup.Morphism H G)
    (ρ : RationalRepresentation G V) (σ : RationalRepresentation H V) : Prop :=
  ∀ h, σ.action h = ρ.action (φ.onPoints h)

/-- The product of two abstract linear actions is their direct-sum action. -/
private lemma directSumRepresentation_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W) :
    ∃ τ : RationalRepresentation K (V × W),
      IsDirectSumRepresentation ρ σ τ := by
  let e (g : Variety.Point K) : (V × W) ≃ₗ[k] (V × W) :=
    LinearEquiv.prodCongr
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ.action g))
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k W (σ.action g))
  let action : Variety.Point K →* LinearMap.GeneralLinearGroup k (V × W) := {
    toFun := fun g =>
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k (V × W)).symm (e g)
    map_one' := by
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (V × W)).injective
      change e 1 = 1
      ext z <;> simp [e]
    map_mul' := by
      intro g h
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (V × W)).injective
      change e (g * h) = e g * e h
      ext z <;> simp [e, map_mul]
    }
  let τ : RationalRepresentation K (V × W) := ⟨action⟩
  refine ⟨τ, ?_⟩
  intro g x y
  rfl

/-- Every invariant submodule induces the abstract quotient action. -/
private lemma quotientRepresentation_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (U : Submodule k V)
    (hU : IsInvariantSubmodule ρ U) :
    ∃ τ : RationalRepresentation K (V ⧸ U), IsQuotientRepresentation ρ U τ := by
  let qmap (g : Variety.Point K) : (V ⧸ U) →ₗ[k] (V ⧸ U) :=
    U.mapQ U (ρ.action g).1 (by
      intro x hx
      exact hU g x hx)
  have qmap_apply (g : Variety.Point K) (x : V) :
      qmap g (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ((ρ.action g).1 x) := by
    rfl
  have qmap_inv_left (g : Variety.Point K) (y : V ⧸ U) :
      qmap g⁻¹ (qmap g y) = y := by
    refine Submodule.Quotient.induction_on U y ?_
    intro x
    rw [qmap_apply, qmap_apply]
    congr 1
    rw [map_inv]
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv k V
      (ρ.action g)).symm
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (ρ.action g)) x) = x
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k V
      (ρ.action g)).symm_apply_apply x
  have qmap_inv_right (g : Variety.Point K) (y : V ⧸ U) :
      qmap g (qmap g⁻¹ y) = y := by
    refine Submodule.Quotient.induction_on U y ?_
    intro x
    rw [qmap_apply, qmap_apply]
    congr 1
    rw [map_inv]
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv k V
      (ρ.action g))
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (ρ.action g)).symm x) = x
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k V
      (ρ.action g)).apply_symm_apply x
  let e (g : Variety.Point K) : (V ⧸ U) ≃ₗ[k] (V ⧸ U) :=
    LinearEquiv.ofBijective (qmap g) (by
      constructor
      · intro x y hxy
        rw [← qmap_inv_left g x, ← qmap_inv_left g y, hxy]
      · intro y
        exact ⟨qmap g⁻¹ y, qmap_inv_right g y⟩)
  let action : Variety.Point K →* LinearMap.GeneralLinearGroup k (V ⧸ U) := {
    toFun := fun g =>
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k (V ⧸ U)).symm (e g)
    map_one' := by
      ext x
      change qmap 1 (Submodule.Quotient.mk x) = Submodule.Quotient.mk x
      rw [qmap_apply]
      simp
    map_mul' := by
      intro g h
      ext x
      change qmap (g * h) (Submodule.Quotient.mk x) =
        qmap g (qmap h (Submodule.Quotient.mk x))
      rw [qmap_apply, qmap_apply, qmap_apply, map_mul]
      rfl
    }
  let τ : RationalRepresentation K (V ⧸ U) := ⟨action⟩
  refine ⟨τ, ?_⟩
  intro g x
  rfl

/-- Every invariant submodule carries the restricted abstract linear action. -/
private lemma restrictionRepresentation_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (U : Submodule k V)
    (hU : IsInvariantSubmodule ρ U) :
    ∃ τ : RationalRepresentation K U, IsRestrictionRepresentation ρ U τ := by
  have hmap (g : Variety.Point K) : ∀ x : U, (ρ.action g).1 x.1 ∈ U := by
    intro x
    exact hU g x.1 x.2
  let e (g : Variety.Point K) : U ≃ₗ[k] U :=
    LinearEquiv.ofBijective ((ρ.action g).1.restrict
      (p := U) (q := U) (fun x hx => hU g x hx)) (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V)
          (ρ.action g)).injective (congrArg Subtype.val hxy)
      · intro y
        have hinvMem : ((ρ.action g)⁻¹).1 y.1 ∈ U := by
          rw [← map_inv ρ.action]
          exact hU g⁻¹ y.1 y.2
        let x : U := ⟨((ρ.action g)⁻¹).1 y.1, hinvMem⟩
        refine ⟨x, ?_⟩
        apply Subtype.ext
        change ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (ρ.action g))
            ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V
              (ρ.action g)).symm y.1)) = y.1
        exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (ρ.action g)).apply_symm_apply y.1)
  let action : Variety.Point K →* LinearMap.GeneralLinearGroup k U := {
    toFun := fun g =>
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k U).symm (e g)
    map_one' := by
      ext x
      change (ρ.action 1).1 x.1 = x.1
      simp
    map_mul' := by
      intro g h
      ext x
      change (ρ.action (g * h)).1 x.1 =
        (ρ.action g).1 ((ρ.action h).1 x.1)
      rw [map_mul]
      rfl
    }
  let τ : RationalRepresentation K U := ⟨action⟩
  refine ⟨τ, ?_⟩
  intro g x
  rfl

public theorem rationalRepresentation_directSum_exists
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (hρ : IsRationalRepresentation ρ) (hσ : IsRationalRepresentation σ) :
    ∃ τ : RationalRepresentation K (V × W),
      IsDirectSumRepresentation ρ σ τ ∧ IsRationalRepresentation τ := by
  rcases hρ with ⟨eV, fV, hfV⟩
  rcases hσ with ⟨eW, fW, hfW⟩
  rcases directSumRepresentation_exists ρ σ with ⟨τ, hτ⟩
  let hdim : Module.finrank k (V × W) =
      Module.finrank k V + Module.finrank k W := Module.finrank_prod
  let idx : (Fin (Module.finrank k V) ⊕ Fin (Module.finrank k W)) ≃
      Fin (Module.finrank k (V × W)) :=
    finSumFinEquiv.trans (Equiv.cast (congrArg Fin hdim.symm))
  let b : Module.Basis (Fin (Module.finrank k (V × W))) k (V × W) :=
    (eV.prod eW).reindex idx
  let matrixCoefficient : Fin (Module.finrank k (V × W)) →
      Fin (Module.finrank k (V × W)) → K.PolynomialFunction := fun i j =>
    match idx.symm i, idx.symm j with
    | Sum.inl iV, Sum.inl jV =>
        rationalRepresentationMatrixCoefficient ρ eV fV iV jV
    | Sum.inr iW, Sum.inr jW =>
        rationalRepresentationMatrixCoefficient σ eW fW iW jW
    | _, _ => 0
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr ((τ.action g : Module.End k (V × W)) (b j)) i := by
    intro i j g
    generalize hi : idx.symm i = i' at *
    generalize hj : idx.symm j = j' at *
    cases i' with
    | inl iV =>
        cases j' with
        | inl jV =>
            simp only [matrixCoefficient, hi, hj]
            rw [rationalRepresentationMatrixCoefficient_apply ρ eV fV hfV]
            rw [show b j = (eV jV, 0) by simp [b, Module.Basis.reindex_apply, hj]]
            rw [hτ]
            simp only [map_zero]
            change _ = (eV.prod eW).repr
              (((ρ.action g : Module.End k V) (eV jV)), 0) (idx.symm i)
            rw [hi]
            simp
        | inr jW =>
            simp only [matrixCoefficient, hi, hj]
            rw [show b j = (0, eW jW) by simp [b, Module.Basis.reindex_apply, hj]]
            rw [hτ]
            simp only [map_zero]
            change 0 = (eV.prod eW).repr
              (0, ((σ.action g : Module.End k W) (eW jW))) (idx.symm i)
            rw [hi]
            simp
    | inr iW =>
        cases j' with
        | inl jV =>
            simp only [matrixCoefficient, hi, hj]
            rw [show b j = (eV jV, 0) by simp [b, Module.Basis.reindex_apply, hj]]
            rw [hτ]
            simp only [map_zero]
            change 0 = (eV.prod eW).repr
              (((ρ.action g : Module.End k V) (eV jV)), 0) (idx.symm i)
            rw [hi]
            simp
        | inr jW =>
            simp only [matrixCoefficient, hi, hj]
            rw [rationalRepresentationMatrixCoefficient_apply σ eW fW hfW]
            rw [show b j = (0, eW jW) by simp [b, Module.Basis.reindex_apply, hj]]
            rw [hτ]
            simp only [map_zero]
            change _ = (eV.prod eW).repr
              (0, ((σ.action g : Module.End k W) (eW jW))) (idx.symm i)
            rw [hi]
            rfl
  let inverseMatrixCoefficient : Fin (Module.finrank k (V × W)) →
      Fin (Module.finrank k (V × W)) → K.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism K)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr (((((τ.action g)⁻¹ : LinearMap.GeneralLinearGroup k (V × W)) :
          Module.End k (V × W))) (b j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b τ.action matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply
  refine ⟨τ, hτ, b, f, ?_⟩
  intro g
  change glPointEquivOf k (V × W) b
    (generalLinearRepresentationPoint b (τ.action g)) = τ.action g
  exact glPointEquivOf_generalLinearRepresentationPoint b (τ.action g)

/-- Pullback along an algebraic-group morphism preserves rationality. -/
public theorem rationalRepresentation_pullback_exists
    [IsAlgClosed k]
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (φ : AlgebraicGroup.Morphism H K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) :
    ∃ τ : RationalRepresentation H V,
      IsPullbackRepresentation φ ρ τ ∧ IsRationalRepresentation τ := by
  let τ : RationalRepresentation H V :=
    ⟨ρ.action.comp φ.onPoints⟩
  refine ⟨τ, ?_, ?_⟩
  · intro h
    rfl
  · obtain ⟨e, f, hf⟩ := hρ
    refine ⟨e, f.comp φ, ?_⟩
    intro h
    exact hf (φ.onPoints h)

public theorem rationalRepresentation_quotient_exists
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (U : Submodule k V) (hU : IsInvariantSubmodule ρ U) :
    ∃ τ : RationalRepresentation K (V ⧸ U),
      IsQuotientRepresentation ρ U τ ∧ IsRationalRepresentation τ := by
  rcases hρ with ⟨e, fρ, hfρ⟩
  rcases quotientRepresentation_exists ρ U hU with ⟨τ, hτ⟩
  let b : Module.Basis (Fin (Module.finrank k (V ⧸ U))) k (V ⧸ U) :=
    Module.finBasis k (V ⧸ U)
  let representative : Fin (Module.finrank k (V ⧸ U)) → V := fun j =>
    Classical.choose (U.mkQ_surjective (b j))
  have representative_spec (j : Fin (Module.finrank k (V ⧸ U))) :
      U.mkQ (representative j) = b j :=
    Classical.choose_spec (U.mkQ_surjective (b j))
  let matrixCoefficient : Fin (Module.finrank k (V ⧸ U)) →
      Fin (Module.finrank k (V ⧸ U)) → K.PolynomialFunction := fun i j =>
    rationalRepresentationLinearMatrixCoefficient ρ e fρ
      ((b.dualBasis i).comp U.mkQ) (representative j)
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr ((τ.action g : Module.End k (V ⧸ U)) (b j)) i := by
    intro i j g
    rw [show matrixCoefficient i j = rationalRepresentationLinearMatrixCoefficient
      ρ e fρ ((b.dualBasis i).comp U.mkQ) (representative j) by rfl]
    rw [rationalRepresentationLinearMatrixCoefficient_apply ρ e fρ hfρ]
    change b.dualBasis i (U.mkQ ((ρ.action g : Module.End k V) (representative j))) = _
    have ht := hτ g (representative j)
    change (τ.action g : Module.End k (V ⧸ U)) (U.mkQ (representative j)) =
      U.mkQ ((ρ.action g : Module.End k V) (representative j)) at ht
    rw [← ht, representative_spec]
    exact Module.Basis.dualBasis_apply b i ((τ.action g : Module.End k (V ⧸ U)) (b j))
  let inverseMatrixCoefficient : Fin (Module.finrank k (V ⧸ U)) →
      Fin (Module.finrank k (V ⧸ U)) → K.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism K)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr (((((τ.action g)⁻¹ : LinearMap.GeneralLinearGroup k (V ⧸ U)) :
          Module.End k (V ⧸ U))) (b j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b τ.action matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply
  refine ⟨τ, hτ, b, f, ?_⟩
  intro g
  change glPointEquivOf k (V ⧸ U) b
    (generalLinearRepresentationPoint b (τ.action g)) = τ.action g
  exact glPointEquivOf_generalLinearRepresentationPoint b (τ.action g)

public theorem rationalRepresentation_restriction_exists
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (U : Submodule k V) (hU : IsInvariantSubmodule ρ U) :
    ∃ τ : RationalRepresentation K U,
      IsRestrictionRepresentation ρ U τ ∧ IsRationalRepresentation τ := by
  rcases hρ with ⟨e, fρ, hfρ⟩
  rcases restrictionRepresentation_exists ρ U hU with ⟨τ, hτ⟩
  let b : Module.Basis (Fin (Module.finrank k U)) k U := Module.finBasis k U
  let matrixCoefficient : Fin (Module.finrank k U) →
      Fin (Module.finrank k U) → K.PolynomialFunction := fun i j =>
    rationalRepresentationLinearMatrixCoefficient ρ e fρ
      (Subspace.dualLift U (b.dualBasis i)) (b j : V)
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr ((τ.action g : Module.End k U) (b j)) i := by
    intro i j g
    rw [show matrixCoefficient i j = rationalRepresentationLinearMatrixCoefficient
      ρ e fρ (Subspace.dualLift U (b.dualBasis i)) (b j : V) by rfl]
    rw [rationalRepresentationLinearMatrixCoefficient_apply ρ e fρ hfρ]
    have ht := hτ g (b j)
    change (((τ.action g : Module.End k U) (b j) : U) : V) =
      (ρ.action g : Module.End k V) (b j : V) at ht
    rw [← ht]
    rw [Subspace.dualLift_of_subtype]
    exact Module.Basis.dualBasis_apply b i ((τ.action g : Module.End k U) (b j))
  let inverseMatrixCoefficient : Fin (Module.finrank k U) →
      Fin (Module.finrank k U) → K.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism K)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr (((((τ.action g)⁻¹ : LinearMap.GeneralLinearGroup k U) :
          Module.End k U)) (b j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b τ.action matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply
  refine ⟨τ, hτ, b, f, ?_⟩
  intro g
  change glPointEquivOf k U b
    (generalLinearRepresentationPoint b (τ.action g)) = τ.action g
  exact glPointEquivOf_generalLinearRepresentationPoint b (τ.action g)

section
variable {k : Type u} [Field k]

@[expose]
public def IsDualRepresentation
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V)
    (σ : RationalRepresentation K (Module.Dual k V)) : Prop :=
  ∀ g f v, (σ.action g).1 f v = f ((ρ.action g⁻¹).1 v)

/-- Every abstract linear action induces the contragredient action on the dual. -/
private lemma dualRepresentation_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) :
    ∃ τ : RationalRepresentation K (Module.Dual k V),
      IsDualRepresentation ρ τ := by
  let e (g : Variety.Point K) : Module.Dual k V ≃ₗ[k] Module.Dual k V :=
    LinearEquiv.dualMap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ.action g⁻¹))
  let action : Variety.Point K →* LinearMap.GeneralLinearGroup k (Module.Dual k V) := {
    toFun := fun g =>
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k (Module.Dual k V)).symm (e g)
    map_one' := by
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (Module.Dual k V)).injective
      change e 1 = 1
      ext f x
      simp [e]
    map_mul' := by
      intro g h
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (Module.Dual k V)).injective
      change e (g * h) = e g * e h
      ext f x
      simp [e, map_mul]
    }
  let τ : RationalRepresentation K (Module.Dual k V) := ⟨action⟩
  refine ⟨τ, ?_⟩
  intro g f x
  change e g f x = _
  simp only [e, LinearEquiv.dualMap_apply]
  congr 1

end

section
variable {k : Type u} [Field k]

@[expose]
public def IsTensorProductRepresentation
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (τ : RationalRepresentation K (TensorProduct k V W)) : Prop :=
  ∀ g v w, (τ.action g).1 (TensorProduct.tmul k v w) =
    TensorProduct.tmul k ((ρ.action g).1 v) ((σ.action g).1 w)

/-- Two abstract linear actions induce the tensor-product action. -/
private lemma tensorProductRepresentation_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W) :
    ∃ τ : RationalRepresentation K (TensorProduct k V W),
      IsTensorProductRepresentation ρ σ τ := by
  let e (g : Variety.Point K) :
      TensorProduct k V W ≃ₗ[k] TensorProduct k V W :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ.action g)).rTensor W).trans
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k W (σ.action g)).lTensor V)
  have e_tmul (g : Variety.Point K) (v : V) (w : W) :
      e g (TensorProduct.tmul k v w) =
        TensorProduct.tmul k ((ρ.action g).1 v) ((σ.action g).1 w) := by
    simp [e]
  let action : Variety.Point K →* LinearMap.GeneralLinearGroup k (TensorProduct k V W) := {
    toFun := fun g =>
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k (TensorProduct k V W)).symm (e g)
    map_one' := by
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (TensorProduct k V W)).injective
      change e 1 = 1
      apply LinearEquiv.toLinearMap_injective
      apply TensorProduct.ext
      ext v w
      simp [e_tmul]
    map_mul' := by
      intro g h
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (TensorProduct k V W)).injective
      change e (g * h) = e g * e h
      apply LinearEquiv.toLinearMap_injective
      apply TensorProduct.ext
      ext v w
      simp [e_tmul, map_mul]
    }
  let τ : RationalRepresentation K (TensorProduct k V W) := ⟨action⟩
  refine ⟨τ, ?_⟩
  intro g v w
  exact e_tmul g v w

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem rationalRepresentation_dual_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) :
    ∃ τ : RationalRepresentation K (Module.Dual k V),
      IsDualRepresentation ρ τ ∧ IsRationalRepresentation τ := by
  rcases hρ with ⟨e, fρ, hfρ⟩
  rcases dualRepresentation_exists ρ with ⟨τ, hτ⟩
  let hdim : Module.finrank k (Module.Dual k V) = Module.finrank k V :=
    Subspace.dual_finrank_eq
  let idx : Fin (Module.finrank k V) ≃
      Fin (Module.finrank k (Module.Dual k V)) :=
    Equiv.cast (congrArg Fin hdim.symm)
  let b : Module.Basis (Fin (Module.finrank k (Module.Dual k V))) k
      (Module.Dual k V) := e.dualBasis.reindex idx
  let matrixCoefficient : Fin (Module.finrank k (Module.Dual k V)) →
      Fin (Module.finrank k (Module.Dual k V)) → K.PolynomialFunction := fun i j =>
    rationalRepresentationInverseMatrixCoefficient ρ e fρ (idx.symm j) (idx.symm i)
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr ((τ.action g : Module.End k (Module.Dual k V)) (b j)) i := by
    intro i j g
    rw [show matrixCoefficient i j =
      rationalRepresentationInverseMatrixCoefficient ρ e fρ (idx.symm j) (idx.symm i) by
        rfl]
    rw [rationalRepresentationInverseMatrixCoefficient_apply ρ e fρ hfρ]
    rw [show b j = e.dualBasis (idx.symm j) by
      exact Module.Basis.reindex_apply e.dualBasis idx j]
    change _ = e.dualBasis.repr
      ((τ.action g : Module.End k (Module.Dual k V))
        (e.dualBasis (idx.symm j))) (idx.symm i)
    rw [Module.Basis.dualBasis_repr]
    rw [hτ]
    simp
  let inverseMatrixCoefficient : Fin (Module.finrank k (Module.Dual k V)) →
      Fin (Module.finrank k (Module.Dual k V)) → K.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism K)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr (((((τ.action g)⁻¹ :
          LinearMap.GeneralLinearGroup k (Module.Dual k V)) :
          Module.End k (Module.Dual k V))) (b j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b τ.action matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply
  refine ⟨τ, hτ, b, f, ?_⟩
  intro g
  change glPointEquivOf k (Module.Dual k V) b
    (generalLinearRepresentationPoint b (τ.action g)) = τ.action g
  exact glPointEquivOf_generalLinearRepresentationPoint b (τ.action g)

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem rationalRepresentation_tensorProduct_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (hρ : IsRationalRepresentation ρ) (hσ : IsRationalRepresentation σ) :
    ∃ τ : RationalRepresentation K (TensorProduct k V W),
      IsTensorProductRepresentation ρ σ τ ∧ IsRationalRepresentation τ := by
  rcases hρ with ⟨eV, fV, hfV⟩
  rcases hσ with ⟨eW, fW, hfW⟩
  rcases tensorProductRepresentation_exists ρ σ with ⟨τ, hτ⟩
  let hdim : Module.finrank k (TensorProduct k V W) =
      Module.finrank k V * Module.finrank k W := Module.finrank_tensorProduct
  let idx : (Fin (Module.finrank k V) × Fin (Module.finrank k W)) ≃
      Fin (Module.finrank k (TensorProduct k V W)) :=
    finProdFinEquiv.trans (Equiv.cast (congrArg Fin hdim.symm))
  let b : Module.Basis (Fin (Module.finrank k (TensorProduct k V W))) k
      (TensorProduct k V W) := (eV.tensorProduct eW).reindex idx
  let matrixCoefficient : Fin (Module.finrank k (TensorProduct k V W)) →
      Fin (Module.finrank k (TensorProduct k V W)) → K.PolynomialFunction := fun i j =>
    rationalRepresentationMatrixCoefficient ρ eV fV (idx.symm i).1 (idx.symm j).1 *
      rationalRepresentationMatrixCoefficient σ eW fW (idx.symm i).2 (idx.symm j).2
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr ((τ.action g : Module.End k (TensorProduct k V W)) (b j)) i := by
    intro i j g
    rw [show matrixCoefficient i j =
      rationalRepresentationMatrixCoefficient ρ eV fV (idx.symm i).1 (idx.symm j).1 *
        rationalRepresentationMatrixCoefficient σ eW fW (idx.symm i).2 (idx.symm j).2 by
          rfl]
    rw [show b j = eV (idx.symm j).1 ⊗ₜ[k] eW (idx.symm j).2 by
      simp [b, Module.Basis.tensorProduct_apply']]
    rw [hτ]
    change _ = (eV.tensorProduct eW).repr
      (((ρ.action g : Module.End k V) (eV (idx.symm j).1)) ⊗ₜ[k]
        ((σ.action g : Module.End k W) (eW (idx.symm j).2))) (idx.symm i)
    change rationalRepresentationMatrixCoefficient ρ eV fV
      (idx.symm i).1 (idx.symm j).1 g *
      rationalRepresentationMatrixCoefficient σ eW fW
        (idx.symm i).2 (idx.symm j).2 g = _
    rw [rationalRepresentationMatrixCoefficient_apply ρ eV fV hfV,
      rationalRepresentationMatrixCoefficient_apply σ eW fW hfW,
      Module.Basis.tensorProduct_repr_tmul_apply]
    exact mul_comm _ _
  let inverseMatrixCoefficient : Fin (Module.finrank k (TensorProduct k V W)) →
      Fin (Module.finrank k (TensorProduct k V W)) → K.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism K)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr (((((τ.action g)⁻¹ :
          LinearMap.GeneralLinearGroup k (TensorProduct k V W)) :
          Module.End k (TensorProduct k V W))) (b j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b τ.action matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply
  refine ⟨τ, hτ, b, f, ?_⟩
  intro g
  change glPointEquivOf k (TensorProduct k V W) b
    (generalLinearRepresentationPoint b (τ.action g)) = τ.action g
  exact glPointEquivOf_generalLinearRepresentationPoint b (τ.action g)

end

section

variable {k : Type u} [Field k]

@[expose]
public noncomputable def exteriorPowerGeneralLinearGroupHom
    {V : Type v} [AddCommGroup V] [Module k V] (i : ℕ) :
    LinearMap.GeneralLinearGroup k V →*
      LinearMap.GeneralLinearGroup k (⋀[k]^i V) where
  toFun g := {
    val := exteriorPower.map i (g.1 : V →ₗ[k] V)
    inv := exteriorPower.map i (g⁻¹.1 : V →ₗ[k] V)
    val_inv := by
      change exteriorPower.map i (g.1 : V →ₗ[k] V) ∘ₗ
        exteriorPower.map i (g⁻¹.1 : V →ₗ[k] V) = LinearMap.id
      rw [← exteriorPower.map_comp]
      have h : (g.1 : V →ₗ[k] V) ∘ₗ (g⁻¹.1 : V →ₗ[k] V) = LinearMap.id :=
        g.val_inv
      rw [h, exteriorPower.map_id]
    inv_val := by
      change exteriorPower.map i (g⁻¹.1 : V →ₗ[k] V) ∘ₗ
        exteriorPower.map i (g.1 : V →ₗ[k] V) = LinearMap.id
      rw [← exteriorPower.map_comp]
      have h : (g⁻¹.1 : V →ₗ[k] V) ∘ₗ (g.1 : V →ₗ[k] V) = LinearMap.id :=
        g.inv_val
      rw [h, exteriorPower.map_id] }
  map_one' := Units.ext <| exteriorPower.map_id (n := i)
  map_mul' g h := Units.ext <| by
    change exteriorPower.map i ((g * h).1 : V →ₗ[k] V) =
      exteriorPower.map i (g.1 : V →ₗ[k] V) *
        exteriorPower.map i (h.1 : V →ₗ[k] V)
    rw [show ((g * h).1 : V →ₗ[k] V) =
      (g.1 : V →ₗ[k] V) ∘ₗ (h.1 : V →ₗ[k] V) by rfl]
    exact exteriorPower.map_comp (n := i) _ _

@[expose]
public noncomputable def exteriorPowerRepresentation
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (i : ℕ) :
    RationalRepresentation K (⋀[k]^i V) where
  action := (exteriorPowerGeneralLinearGroupHom i).comp ρ.action

end

section

variable {k : Type u} [Field k]

public lemma exteriorPowerRepresentation_action
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (i : ℕ) (g : Variety.Point K)
    (x : ⋀[k]^i V) :
    ((exteriorPowerRepresentation ρ i).action g).1 x =
      exteriorPower.map i ((ρ.action g).1 : V →ₗ[k] V) x := by
  rfl

end

end Theory.AlgebraicGroup
