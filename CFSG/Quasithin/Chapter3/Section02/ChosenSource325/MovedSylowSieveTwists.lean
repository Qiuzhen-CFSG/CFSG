module
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientTwist

/-!
# Homogeneous invariance from the actual characteristic-kernel model

When the fixed part of a seed is zero, its inclusion in the central quotient
is an equivariant equivalence. A characteristic action kernel makes ambient
conjugation descend to the same model group. Model automorphism intertwiners
then fix the literal homogeneous seed by A.1.42.

The chosen-seed application is `SeedAlternativesMovedSylowSieve`.
Source: Aschbacher--Smith A.1.40--42 and D.3.5(5), combined manuscript
of 1 March 2004, printed pp.31--32 and195--196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {G V P W : Type*} [Group G] [Group P]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V)

/-- A seed with zero fixed space is equivariantly identified with its literal
image in the quotient by the ambient fixed space. -/
def zeroFixedImageEquiv (X : Subgroup G) (I : Submodule (ZMod 2) V)
    (hI : X ≤ subspaceStabilizer ρ I) (hz : I ⊓ fixedSpace ρ X = ⊥) :
    Representation.Equiv (invariantSubspace ρ X I hI).toRepresentation
      (quotientImage ρ X I hI).toRepresentation := by
  let S := quotientImage ρ X I hI
  let q : I →ₗ[ZMod 2] S.toSubmodule :=
    ((fixedSpace ρ X).mkQ.comp I.subtype).codRestrict S.toSubmodule
      (fun v => ⟨v,v.property,rfl⟩)
  have hi : Function.Injective q := by
    apply (injective_iff_map_eq_zero q).mpr
    intro v hv
    have hc : v.val ∈ fixedSpace ρ X := (Submodule.Quotient.mk_eq_zero _).mp
      (congrArg Subtype.val hv)
    exact Subtype.ext (show v.val = 0 from (hz.le ⟨v.property,hc⟩))
  have hs : Function.Surjective q := by
    rintro ⟨v,w,hw,rfl⟩
    exact ⟨⟨w,hw⟩,rfl⟩
  refine Representation.Equiv.mk (LinearEquiv.ofBijective q ⟨hi,hs⟩) ?_
  intro x
  apply LinearMap.ext
  intro v
  rfl

/-- A characteristic-kernel model whose every automorphism twist is equivalent
fixes the actual homogeneous seed when its fixed space is zero. -/
theorem homogeneous_invariant_of_model_twists
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I) (hz : I ⊓ fixedSpace ρ X = ⊥)
    (f : X →* P) (hf : Function.Surjective f) [f.ker.Characteristic]
    (τ : Representation (ZMod 2) P W)
    (b : Representation.Equiv (invariantSubspace ρ X I hI.invariant).toRepresentation
      (τ.comp f))
    (htwist : ∀ a : MulAut P, ∃ d : W ≃ₗ[ZMod 2] W,
      ∀ g v, d (τ g v) = τ (a g) (d v)) :
    T ≤ subspaceStabilizer ρ I := by
  let q := QuotientGroup.quotientKerEquivOfSurjective f hf
  let e := (zeroFixedImageEquiv ρ X I hI.invariant hz).symm.trans b
  intro t ht
  apply (subspace_map_eq_iff ρ I t).mp
  exact hI.map_eq_of_quotient_model_twist ρ ⟨t,ht⟩ f.ker q τ e htwist

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
