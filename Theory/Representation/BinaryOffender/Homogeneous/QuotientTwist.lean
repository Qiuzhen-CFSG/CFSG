module
public import Theory.Representation.BinaryOffender.Homogeneous.AutomorphismTwist
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-!
# Homogeneous seed stability from a characteristic quotient model

An automorphism-invariant model for the central seed quotient corrects the
normalizer action to an actual module isomorphism. Homogeneous uniqueness then
fixes the original seed itself. The quotient marking and its conjugation action
are retained explicitly. This removes the deleted-square alternative from a
moved A5 seed orbit, using its concrete symmetric wreath intertwiners.

Source: Aschbacher–Smith A.1.40–42 and D.3.5, printed pp.31–32 and195–196.
-/

public section
open Subgroup
namespace Representation.BinaryOffender.Homogeneous
variable {G V P W : Type*} [Group G] [Group P]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V)

/-- Automorphism invariance of a characteristic quotient model fixes the
original homogeneous seed, not merely its image modulo fixed vectors. -/
theorem IsIrrPlusWith.map_eq_of_quotient_model_twist
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I) (t : T)
    (N : Subgroup X) [N.Characteristic] (q : (X ⧸ N) ≃* P)
    (τ : Representation (ZMod 2) P W)
    (b : (quotientImage ρ X I hI.invariant).toRepresentation.Equiv
      (τ.comp (q.toMonoidHom.comp (QuotientGroup.mk' N))))
    (htwist : ∀ a : MulAut P, ∃ d : W ≃ₗ[ZMod 2] W,
      ∀ g v, d (τ g v) = τ (a g) (d v)) :
    I.map (ρ t.val) = I := by
  let S := quotientImage ρ X I hI.invariant
  let n := X.normalizerMonoidHom
    ⟨t.val⁻¹, hI.normalizes (T.inv_mem t.property)⟩
  let a := q.symm.trans ((quotientAut N n).trans q)
  obtain ⟨d,hd⟩ := htwist a
  let c := b.toLinearEquiv.trans (d.trans b.toLinearEquiv.symm)
  have hb (x : X) (v : S.toSubmodule) :
      b (S.toRepresentation x v) = τ (q (QuotientGroup.mk' N x)) (b v) :=
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap x v
  have hc (v : S.toSubmodule) : b (c v) = d (b v) := b.toLinearEquiv.apply_symm_apply _
  apply hI.map_eq_of_central_twist ρ t c
  intro x v
  apply b.injective
  change b (c (S.toRepresentation x v)) = b (S.toRepresentation (n x) (c v))
  rw [hc,hb,hb,hc,hd]
  change τ (q (quotientAut N n (q.symm (q (QuotientGroup.mk' N x))))) _ = _
  rw [q.symm_apply_apply,quotientAut_apply_mk]
end Representation.BinaryOffender.Homogeneous
