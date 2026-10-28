module

public import Theory.AlgebraicGroup.RootSubgroups.Tangent
public import Theory.AlgebraicGroup.ClosedSubgroup.VanishingIdeal

/-!
# Reduced one-parameter curve integrability

This module isolates the characteristic-sensitive passage from an identity
tangent containment to containment of an additive one-parameter curve.  The
tangent hypothesis is expressed by the range of the identity differential of
the closed subgroup inclusion, and the second hypothesis is a relative
separability (or Frobenius-saturation) condition: an ambient equation of the
closed subgroup whose pullback to the additive parameter has zero differential
must already have zero pullback.  The latter condition is necessary in positive
characteristic, where the Frobenius curve `t ↦ t ^ p` has zero tangent but is
not constant.  The proof uses the vanishing-ideal tangent criterion and the
closed-subgroup zero-locus API.  The polynomial-function coordinate rings used
by carrier varieties are reduced by the existing
`Variety.polynomialFunction_isReduced` instance; no source-numbered theorem or
inseparable differential-surjectivity assertion is used.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/--
The relative separability condition for an additive curve and a closed
subgroup.  It rules out precisely the Frobenius obstruction: every equation of
`N` whose pullback along the curve has zero additive differential has zero
pullback as a polynomial function on `KPlus k`.
-/
@[expose]
public def OneParameterVanishingFrobeniusSaturated
    {K : Variety k} [AlgebraicGroup K] [IsAlgClosed k]
    (N X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety) : Prop :=
  ∀ f : Variety.PolynomialFunction K, f ∈ N.vanishingIdeal →
    oneParameterTangent X x f = 0 →
      (X.inclusion.comp x.hom).toVariety.pullbackAlgHom f = 0

private lemma identityTangent_zero_on_vanishingIdeal_of_mem_range
    {K : Variety k} [AlgebraicGroup K] [IsAlgClosed k]
    (N : ClosedSubgroup K) (D : IdentityPointDerivation K)
    (hD : D ∈ LinearMap.range (identityTangentMorphismLinearMap N.inclusion)) :
    ∀ f ∈ N.vanishingIdeal, D f = 0 := by
  rintro f hf
  rcases hD with ⟨E, rfl⟩
  rw [identityTangentMorphismLinearMap_apply]
  change E (N.restrictionRingHom f) = 0
  rw [hf, map_zero]

/--
An additive one-parameter curve with tangent in the identity-tangent range of
`N` is contained in `N` whenever the curve is relatively separable along the
vanishing ideal of `N`.  The displayed range conclusion is equivalent to the
pointwise subgroup containment of the associated ambient morphism.
-/
public theorem oneParameter_range_le_of_tangent_mem_of_vanishingFrobeniusSaturated
    {K : Variety k} [AlgebraicGroup K] [IsAlgClosed k]
    (N X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (htangent : oneParameterTangent X x ∈
      LinearMap.range (identityTangentMorphismLinearMap N.inclusion))
    (hsaturated : OneParameterVanishingFrobeniusSaturated N X x) :
    Set.range (fun t : k => X.includePoint (x.value t)) ⊆
      (N.toSubgroup : Set (Variety.Point K)) := by
  intro y hy
  rcases hy with ⟨t, rfl⟩
  change X.includePoint (x.value t) ∈ (N.toSubgroup : Set (Variety.Point K))
  apply (N.mem_iff_forall_vanishingIdeal
    (X.includePoint (x.value t))).2
  intro f hf
  have hvanishing : ∀ g ∈ N.vanishingIdeal, oneParameterTangent X x g = 0 :=
    identityTangent_zero_on_vanishingIdeal_of_mem_range N
      (oneParameterTangent X x) htangent
  have hpull := hsaturated f hf (hvanishing f hf)
  have heval := congrArg
    (fun q : Variety.PolynomialFunction (KPlus k) => q (kPlusPoint t)) hpull
  change f (X.includePoint (x.value t)) = 0 at heval
  exact heval

/-- The range form and the subgroup form of one-parameter containment agree. -/
public theorem oneParameter_range_le_iff_mem
    {K : Variety k} [AlgebraicGroup K]
    (N X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety) :
    Set.range (fun t : k => X.includePoint (x.value t)) ⊆
        (N.toSubgroup : Set (Variety.Point K)) ↔
      ∀ t : k, X.includePoint (x.value t) ∈ N.toSubgroup := by
  constructor
  · intro h t
    exact h ⟨t, rfl⟩
  · intro h y hy
    rcases hy with ⟨t, rfl⟩
    exact h t

end Theory.AlgebraicGroup
