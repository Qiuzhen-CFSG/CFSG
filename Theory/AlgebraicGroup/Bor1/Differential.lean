module

public import Mathlib.RingTheory.Derivation.Basic
public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSetFinite

/-!
# Identity-point differentials of algebraic-group morphisms

This module represents the tangent space at the identity by derivations of the
coordinate algebra.  Coordinate evaluation embeds that tangent space in a
finite-dimensional function space, while pullback along algebraic-group
morphisms gives the functorial identity differential.  It also develops the
conjugation action and the kernel/range comparisons used by the Bor1 and Lang
arguments.  The coordinate and conjugation maps are exposed together with
evaluation lemmas because downstream modules compare their defining pullbacks
when constructing equivariant finite-dimensional models.
-/

universe u

set_option linter.unusedSectionVars false

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! The tangent space at the identity, represented by derivations of the
coordinate algebra into the residue field at the identity.  Bor1 uses this
space to formulate separability of orbit maps. -/

public noncomputable instance identityPointModule (K : Variety k) [AlgebraicGroup K] :
    Module (Variety.PolynomialFunction K) k :=
  Module.compHom k (polynomialFunctionPointAlgHom K 1).toRingHom

public noncomputable abbrev IdentityPointDerivation
    (K : Variety k) [AlgebraicGroup K] :=
    Derivation k (Variety.PolynomialFunction K) k

/-! Coordinate functions determine a derivation.  This gives the finite
dimensionality needed for the linear representation used in Bor1. -/

@[expose] public noncomputable def coordinateTangentMap
    (K : Variety k) [AlgebraicGroup K] :
    IdentityPointDerivation K →ₗ[k] K.Coordinates → k where
  toFun D i := D (Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] public theorem coordinateTangentMap_apply
    (K : Variety k) [AlgebraicGroup K]
    (D : IdentityPointDerivation K) (i : K.Coordinates) :
    coordinateTangentMap K D i =
      D (Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X i)) := rfl

omit [IsAlgClosed k] in
public lemma coordinateTangentMap_injective (K : Variety k) [AlgebraicGroup K] :
    Function.Injective (coordinateTangentMap K) := by
  intro D E hDE
  apply Derivation.ext_of_adjoin_eq_top
    (Set.range fun i : K.Coordinates ↦
      Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X i))
  · rw [Algebra.adjoin_range_eq_range_aeval]
    apply (AlgHom.range_eq_top _).2
    intro f
    obtain ⟨p, hp⟩ := f.representedBy
    refine ⟨p, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    rw [hp]
    have haeval :
        MvPolynomial.aeval (fun i : K.Coordinates ↦
          Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X i)) =
          evaluationAlgHom K := by
      apply MvPolynomial.algHom_ext
      intro i
      apply Variety.PolynomialFunction.ext
      intro y
      rw [MvPolynomial.aeval_X]
      rfl
    rw [haeval]
    rfl
  · rintro _ ⟨i, rfl⟩
    exact congrFun hDE i

public noncomputable instance identityPointDerivationFiniteDimensional
    (K : Variety k) [AlgebraicGroup K] :
    FiniteDimensional k (IdentityPointDerivation K) :=
  FiniteDimensional.of_injective (coordinateTangentMap K)
    (coordinateTangentMap_injective K)

/-! Conjugation transports tangent vectors at the identity. -/

@[expose] public noncomputable def identityTangentConjugationLinearMap
    (K : Variety k) [AlgebraicGroup K] (g : Variety.Point K) :
    IdentityPointDerivation K →ₗ[k] IdentityPointDerivation K where
  toFun D := {
    toLinearMap := D.toLinearMap.comp
      (AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom.toLinearMap
    map_one_eq_zero' := by simp
    leibniz' := by
      intro f h
      change D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom (f * h)) =
        f • D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom h) +
          h • D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f)
      rw [map_mul, Derivation.leibniz]
      change f ((AlgebraicGroup.conjugationByMorphism K g).toFun 1) *
            D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom h) +
          h ((AlgebraicGroup.conjugationByMorphism K g).toFun 1) *
            D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f) =
        f 1 * D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom h) +
          h 1 * D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f)
      rw [AlgebraicGroup.conjugationByMorphism_apply]
      simp }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] public theorem identityTangentConjugationLinearMap_apply
    (K : Variety k) [AlgebraicGroup K] (g : Variety.Point K)
    (D : IdentityPointDerivation K) (a : Variety.PolynomialFunction K) :
    identityTangentConjugationLinearMap K g D a =
      D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom a) := rfl

omit [IsAlgClosed k] in
public lemma identityTangentConjugationLinearMap_one
    (K : Variety k) [AlgebraicGroup K] :
    identityTangentConjugationLinearMap K 1 = LinearMap.id := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro f
  change D ((AlgebraicGroup.conjugationByMorphism K 1).pullbackAlgHom f) = D f
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change f ((AlgebraicGroup.conjugationByMorphism K 1).toFun x) = f x
  rw [AlgebraicGroup.conjugationByMorphism_apply]
  simp

omit [IsAlgClosed k] in
public lemma identityTangentConjugationLinearMap_mul
    (K : Variety k) [AlgebraicGroup K] (g h : Variety.Point K) :
    identityTangentConjugationLinearMap K (g * h) =
      (identityTangentConjugationLinearMap K g).comp
        (identityTangentConjugationLinearMap K h) := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro f
  change D ((AlgebraicGroup.conjugationByMorphism K (g * h)).pullbackAlgHom f) =
    D ((AlgebraicGroup.conjugationByMorphism K h).pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f))
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change f ((AlgebraicGroup.conjugationByMorphism K (g * h)).toFun x) =
    f ((AlgebraicGroup.conjugationByMorphism K g).toFun
      ((AlgebraicGroup.conjugationByMorphism K h).toFun x))
  simp only [AlgebraicGroup.conjugationByMorphism_apply]
  congr 1
  group

public noncomputable def identityTangentRepresentation
    (K : Variety k) [AlgebraicGroup K] :
    RationalRepresentation K (IdentityPointDerivation K) where
  action := {
    toFun := fun g ↦ {
      val := identityTangentConjugationLinearMap K g
      inv := identityTangentConjugationLinearMap K g⁻¹
      val_inv := by
        change (identityTangentConjugationLinearMap K g).comp
          (identityTangentConjugationLinearMap K g⁻¹) = LinearMap.id
        rw [← identityTangentConjugationLinearMap_mul, mul_inv_cancel,
          identityTangentConjugationLinearMap_one]
      inv_val := by
        change (identityTangentConjugationLinearMap K g⁻¹).comp
          (identityTangentConjugationLinearMap K g) = LinearMap.id
        rw [← identityTangentConjugationLinearMap_mul, inv_mul_cancel,
          identityTangentConjugationLinearMap_one] }
    map_one' := by
      apply Units.ext
      exact identityTangentConjugationLinearMap_one K
    map_mul' := by
      intro g h
      apply Units.ext
      exact identityTangentConjugationLinearMap_mul K g h }

/-! Pullback of derivations along an algebraic-group morphism. -/

@[expose] public noncomputable def identityTangentMorphismLinearMap
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K) :
    IdentityPointDerivation H →ₗ[k] IdentityPointDerivation K where
  toFun D := {
    toLinearMap := D.toLinearMap.comp f.toVariety.pullbackAlgHom.toLinearMap
    map_one_eq_zero' := by simp
    leibniz' := by
      intro p q
      change D (f.toVariety.pullbackAlgHom (p * q)) =
        p • D (f.toVariety.pullbackAlgHom q) +
          q • D (f.toVariety.pullbackAlgHom p)
      rw [map_mul, Derivation.leibniz]
      change p (f.onPoints 1) * D (f.toVariety.pullbackAlgHom q) +
          q (f.onPoints 1) * D (f.toVariety.pullbackAlgHom p) =
        p 1 * D (f.toVariety.pullbackAlgHom q) +
          q 1 * D (f.toVariety.pullbackAlgHom p)
      rw [map_one] }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] public theorem identityTangentMorphismLinearMap_apply
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K)
    (D : IdentityPointDerivation H)
    (a : Variety.PolynomialFunction K) :
    identityTangentMorphismLinearMap f D a =
      D (f.toVariety.pullbackAlgHom a) := rfl

/-! The differential of a closed-subgroup inclusion is injective. -/

public theorem identityTangentMorphismLinearMap_inclusion_injective
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Function.Injective
      (identityTangentMorphismLinearMap H.inclusion) := by
  intro D E hDE
  apply Derivation.ext
  intro a
  obtain ⟨b, hb⟩ := H.restrictionRingHom_surjective a
  have h := congrArg (fun T : IdentityPointDerivation G => T b) hDE
  change D (H.restrictionRingHom b) = E (H.restrictionRingHom b) at h
  simpa [hb] using h

/-! A morphism whose point kernel contains `H` kills the tangent space of
`H` after composing with the inclusion. -/

public theorem identityTangentMorphismLinearMap_comp_inclusion_eq_zero_of_kernel_le
    {G I : Variety k} [AlgebraicGroup G] [AlgebraicGroup I]
    (H : ClosedSubgroup G) (φ : AlgebraicGroup.Morphism G I)
    (hφ : H.toSubgroup ≤ φ.kernel) :
    ∀ D : IdentityPointDerivation H.carrierVariety,
      identityTangentMorphismLinearMap φ
          (identityTangentMorphismLinearMap H.inclusion D) = 0 := by
  intro D
  apply Derivation.ext
  intro a
  change D (H.inclusion.toVariety.pullbackAlgHom
    (φ.toVariety.pullbackAlgHom a)) = 0
  have hpull : H.inclusion.toVariety.pullbackAlgHom
      (φ.toVariety.pullbackAlgHom a) =
      (algebraMap k (Variety.PolynomialFunction H.carrierVariety))
        (a 1) := by
    apply Variety.PolynomialFunction.ext
    intro x
    change a (φ.onPoints (H.inclusion.onPoints x)) = _
    have hx : H.inclusion.onPoints x ∈ H.toSubgroup := by
      change H.inclusion.onPoints x ∈
        (H.toSubgroup : Set (Variety.Point G))
      rw [← H.range_inclusion]
      exact ⟨x, rfl⟩
    have hkernel : φ.onPoints (H.inclusion.onPoints x) = 1 := hφ hx
    rw [hkernel]
    simp [polynomialFunction_algebraMap_apply]
  rw [hpull]
  exact D.map_algebraMap _

public theorem identityTangentMorphismLinearMap_range_inclusion_le_ker_of_kernel_le
    {G I : Variety k} [AlgebraicGroup G] [AlgebraicGroup I]
    (H : ClosedSubgroup G) (φ : AlgebraicGroup.Morphism G I)
    (hφ : H.toSubgroup ≤ φ.kernel) :
    LinearMap.range (identityTangentMorphismLinearMap H.inclusion) ≤
      LinearMap.ker (identityTangentMorphismLinearMap φ) := by
  rintro _ ⟨D, rfl⟩
  exact identityTangentMorphismLinearMap_comp_inclusion_eq_zero_of_kernel_le
    H φ hφ D

public theorem identityTangentMorphismLinearMap_comp_inclusion_eq_zero
    {G I : Variety k} [AlgebraicGroup G] [AlgebraicGroup I]
    (H : ClosedSubgroup G) (φ : AlgebraicGroup.Morphism G I)
    (hφ : H.toSubgroup ≤ φ.kernel) :
    (identityTangentMorphismLinearMap φ).comp
        (identityTangentMorphismLinearMap H.inclusion) = 0 := by
  ext D a
  exact congrArg (fun T : IdentityPointDerivation I => T a)
    (identityTangentMorphismLinearMap_comp_inclusion_eq_zero_of_kernel_le
      H φ hφ D)

public theorem identityTangentMorphismLinearMap_comp
    {H K L : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    [AlgebraicGroup L]
    (f : AlgebraicGroup.Morphism H K)
    (g : AlgebraicGroup.Morphism K L) :
    identityTangentMorphismLinearMap (g.comp f) =
      (identityTangentMorphismLinearMap g).comp
        (identityTangentMorphismLinearMap f) := by
  ext D a
  rfl

/-! Kernels of differentials compose by the usual preimage formula. -/

public theorem identityTangentMorphismLinearMap_ker_comp
    {H K L : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    [AlgebraicGroup L]
    (f : AlgebraicGroup.Morphism H K)
    (g : AlgebraicGroup.Morphism K L) :
    LinearMap.ker (identityTangentMorphismLinearMap (g.comp f)) =
      Submodule.comap (identityTangentMorphismLinearMap f)
        (LinearMap.ker (identityTangentMorphismLinearMap g)) := by
  rw [identityTangentMorphismLinearMap_comp]
  exact LinearMap.ker_comp _ _

@[simp] public theorem identityTangentMorphismLinearMap_id
    {K : Variety k} [AlgebraicGroup K] :
    identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.id K) =
      LinearMap.id := by
  ext D a
  rfl

public theorem identityTangentMorphismLinearMap_conjugation_naturality
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K) (g : Variety.Point H) :
    (identityTangentMorphismLinearMap f).comp
        (identityTangentConjugationLinearMap H g) =
      (identityTangentConjugationLinearMap K (f.onPoints g)).comp
        (identityTangentMorphismLinearMap f) := by
  ext D a
  change D ((AlgebraicGroup.conjugationByMorphism H g).pullbackAlgHom
      (f.toVariety.pullbackAlgHom a)) =
    D (f.toVariety.pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism K (f.onPoints g)).pullbackAlgHom a))
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change a (f.onPoints (g * x * g⁻¹)) =
    a (f.onPoints g * f.onPoints x * (f.onPoints g)⁻¹)
  simp only [f.onPoints.map_mul, f.onPoints.map_inv]

public theorem identityTangentMorphismLinearMap_ker_conj_invariant
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K) (g : Variety.Point H)
    {D : IdentityPointDerivation H}
    (hD : identityTangentMorphismLinearMap f D = 0) :
    identityTangentMorphismLinearMap f
        (identityTangentConjugationLinearMap H g D) = 0 := by
  have hnat := LinearMap.congr_fun
    (identityTangentMorphismLinearMap_conjugation_naturality f g) D
  change ((identityTangentMorphismLinearMap f).comp
      (identityTangentConjugationLinearMap H g)) D = 0
  rw [hnat]
  simp [hD]

/-! The kernel of a differential is a conjugation-stable tangent subspace. -/

public theorem identityTangentMorphismLinearMap_ker_map_conj_le
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K) (g : Variety.Point H) :
    Submodule.map (identityTangentConjugationLinearMap H g)
        (LinearMap.ker (identityTangentMorphismLinearMap f)) ≤
      LinearMap.ker (identityTangentMorphismLinearMap f) := by
  rintro y ⟨D, hD, rfl⟩
  change identityTangentMorphismLinearMap f
      (identityTangentConjugationLinearMap H g D) = 0
  apply identityTangentMorphismLinearMap_ker_conj_invariant f g
  exact hD

public theorem identityTangentMorphismLinearMap_ker_map_conj_eq
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K) (g : Variety.Point H) :
    Submodule.map (identityTangentConjugationLinearMap H g)
        (LinearMap.ker (identityTangentMorphismLinearMap f)) =
      LinearMap.ker (identityTangentMorphismLinearMap f) := by
  apply le_antisymm
  · exact identityTangentMorphismLinearMap_ker_map_conj_le f g
  · intro D hD
    let g' := g⁻¹
    have hD' := identityTangentMorphismLinearMap_ker_conj_invariant f g' hD
    refine ⟨identityTangentConjugationLinearMap H g' D, hD', ?_⟩
    change ((identityTangentConjugationLinearMap H g).comp
      (identityTangentConjugationLinearMap H g⁻¹)) D = D
    rw [← identityTangentConjugationLinearMap_mul, mul_inv_cancel,
      identityTangentConjugationLinearMap_one]
    rfl

/-! The dimension endpoint of Bor1 §6.7.  The inclusion of a subgroup gives
one containment of tangent spaces; equality of dimensions upgrades it to the
exact differential-kernel statement used in the separability criterion. -/

public theorem identityTangentMorphismLinearMap_ker_eq_range_inclusion_of_finrank_eq
    {G I : Variety k} [AlgebraicGroup G] [AlgebraicGroup I]
    (H : ClosedSubgroup G) (φ : AlgebraicGroup.Morphism G I)
    (hφ : H.toSubgroup ≤ φ.kernel)
    (hdim : Module.finrank k
      (LinearMap.ker (identityTangentMorphismLinearMap φ)) =
      Module.finrank k (IdentityPointDerivation H.carrierVariety)) :
    LinearMap.ker (identityTangentMorphismLinearMap φ) =
      LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
  have hle := identityTangentMorphismLinearMap_range_inclusion_le_ker_of_kernel_le
    H φ hφ
  have hfinrankRange : Module.finrank k
      (LinearMap.range (identityTangentMorphismLinearMap H.inclusion)) =
      Module.finrank k (IdentityPointDerivation H.carrierVariety) :=
    LinearMap.finrank_range_of_inj
      (identityTangentMorphismLinearMap_inclusion_injective H)
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  exact hfinrankRange.trans hdim.symm

end Theory.AlgebraicGroup.Bor1
