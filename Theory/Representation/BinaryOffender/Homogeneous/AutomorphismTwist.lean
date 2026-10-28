module
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientOrbit
public import Theory.Representation.Quotient

/-!
# A homogeneous seed from an invariant central module type

A linear operator intertwining the central image with its inverse conjugation
twist corrects the normalizer action to an actual module isomorphism.
Homogeneity then identifies the original seed with its conjugate. A kernel
supplement also allows irreducibility to be restricted to the active factor.

Source: Aschbacher–Smith, A.1.40–42 and D.3.6, printed pp.31–32 and196.
-/

@[expose] public section
open Subgroup
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem IsIrrPlusWith.map_eq_of_central_twist
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I) (t : T)
    (c : (quotientImage ρ X I hI.invariant).toSubmodule ≃ₗ[ZMod 2]
      (quotientImage ρ X I hI.invariant).toSubmodule)
    (hc : ∀ (x : X) v,
      c ((quotientImage ρ X I hI.invariant).toRepresentation x v) =
        (quotientImage ρ X I hI.invariant).toRepresentation
          (X.normalizerMonoidHom ⟨(t : G)⁻¹, hI.normalizes (T.inv_mem t.property)⟩ x) (c v)) :
    I.map (ρ t.val) = I := by
  let S := quotientImage ρ X I hI.invariant
  let hJ := hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)
  let J := quotientImage ρ X (I.map (ρ t.val)) hJ.choose
  let τ := normalizerQuotientRepresentation ρ X
  let tN : normalizer (X : Set G) := ⟨t.val, hI.normalizes t.property⟩
  have hm : S.toSubmodule.map (τ tN) = J.toSubmodule :=
    (quotientImage_map_normalizer ρ X I tN).symm
  let a := (Submodule.equivMapOfInjective (τ tN) (τ.apply_bijective tN).1 S.toSubmodule).trans
    (LinearEquiv.ofEq _ _ hm)
  have ha (v : S.toSubmodule) : (a v : V ⧸ fixedSpace ρ X) = τ tN v := rfl
  have hcomm (x : X) (w : V ⧸ fixedSpace ρ X) :
      τ tN (fixedQuotientRepresentation ρ X
        (X.normalizerMonoidHom ⟨(t : G)⁻¹, hI.normalizes (T.inv_mem t.property)⟩ x) w) =
      fixedQuotientRepresentation ρ X x (τ tN w) := by
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
      change (fixedSpace ρ X).mkQ (ρ t.val (ρ (X.normalizerMonoidHom
        ⟨(t : G)⁻¹, hI.normalizes (T.inv_mem t.property)⟩ x).val w)) =
        (fixedSpace ρ X).mkQ (ρ x.val (ρ t.val w))
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp only [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left]
  apply hI.eq_of_isomorphic_conjugate ρ t
  refine ⟨c.trans a, ?_⟩
  intro x v
  apply Subtype.ext
  change (a (c (S.toRepresentation x v))).val =
    fixedQuotientRepresentation ρ X x (a (c v)).val
  rw [hc, ha, ha]
  exact hcomm x (c v).val

end Representation.BinaryOffender.Homogeneous

namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem irreducible_restrict_of_sup_kernel [ρ.IsIrreducible]
    (A B : Subgroup G) (hab : A ⊔ B = ⊤) (hb : B ≤ ρ.ker) :
    IsIrreducible (ρ.comp A.subtype) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨?_⟩
  intro P
  have hs : A ⊔ B ≤ BinaryOffender.subspaceStabilizer ρ P.toSubmodule := by
    apply sup_le
    · apply BinaryOffender.le_subspaceStabilizer
      intro g hg v hv
      exact P.apply_mem_toSubmodule ⟨g, hg⟩ hv
    · apply BinaryOffender.le_subspaceStabilizer
      intro g hg v hv
      have he := MonoidHom.mem_ker.mp (hb hg)
      simpa only [he, Module.End.one_apply] using hv
  rw [hab] at hs
  let R : Subrepresentation ρ := ⟨P.toSubmodule, fun g v hv => (hs (mem_top g) v).2 hv⟩
  rcases eq_bot_or_eq_top R with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) h

end Representation
