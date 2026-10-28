module

public import Theory.Representation.BinaryOffender.SectionLinear
public import Mathlib.RepresentationTheory.Invariants

/-!
# Odd-order exactness of binary fixed spaces

Summing the translates of a lift gives an invariant lift through any surjective
equivariant linear map: an odd integer is one in the binary field. Rank-nullity
then makes fixed dimensions additive on invariant subspaces and quotients.

This supplies the averaging step for the native Mathieu spectrum in
Aschbacher–Smith, H.13 (printed pp.395–396) and H.15.7 (printed pp.401–402).
-/

@[expose] public section

open scoped BigOperators
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Odd-order averaging preserves surjectivity on fixed spaces. -/
theorem fixedSpace_map_eq_of_odd (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hs : Function.Surjective f)
    (A : Subgroup G) [Finite A] (ho : Odd (Nat.card A)) :
    (fixedSpace ρ A).map f = fixedSpace σ A := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hc : (Fintype.card A : ZMod 2) = 1 := by
    exact (show Odd (Fintype.card A) by simpa only [Nat.card_eq_fintype_card] using ho).natCast_zmod_two
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩ a
    change σ a (f v) = f v
    exact (hf a v).symm.trans (congrArg f (hv a))
  · intro w hw
    obtain ⟨v, rfl⟩ := hs w
    refine ⟨Representation.norm (ρ.comp A.subtype) v, fun a => Representation.self_norm_apply _ a v, ?_⟩
    simp only [Representation.norm, LinearMap.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply]
    simp only [map_sum, hf, show ∀ a : A, σ a (f v) = f v from hw,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hc, one_smul]

/-- Rank-nullity for the map on fixed spaces of an odd-order subgroup. -/
theorem finrank_fixedSpace_surjection_of_odd [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (f : V →ₗ[ZMod 2] W) (hf : ∀ g v, f (ρ g v) = σ g (f v))
    (hs : Function.Surjective f) (A : Subgroup G) [Finite A] (ho : Odd (Nat.card A)) :
    Module.finrank (ZMod 2) (fixedSpace σ A) +
      Module.finrank (ZMod 2) (LinearMap.ker f ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) =
      Module.finrank (ZMod 2) (fixedSpace ρ A) := by
  let C := fixedSpace ρ A
  let r := f.domRestrict C
  have hr : LinearMap.range r = fixedSpace σ A := by
    change (f.comp C.subtype).range = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact fixedSpace_map_eq_of_odd ρ σ f hf hs A ho
  let e : LinearMap.ker r ≃ₗ[ZMod 2]
      (LinearMap.ker f ⊓ C : Submodule (ZMod 2) V) :=
    { toFun := fun v => ⟨v.val, v.property, v.val.property⟩
      invFun := fun v => ⟨⟨v, v.property.2⟩, v.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hn := r.finrank_range_add_finrank_ker
  rw [hr, e.finrank_eq] at hn
  exact hn

/-- Fixed dimensions are additive across an invariant quotient at odd order. -/
theorem finrank_fixedSpace_quotient_of_odd [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (U : Subrepresentation ρ)
    (A : Subgroup G) [Finite A] (ho : Odd (Nat.card A)) :
    Module.finrank (ZMod 2) (fixedSpace U.quotientRepresentation A) +
      Module.finrank (ZMod 2) (fixedSpace U.toRepresentation A) =
      Module.finrank (ZMod 2) (fixedSpace ρ A) := by
  have h := finrank_fixedSpace_surjection_of_odd ρ U.quotientRepresentation U.toSubmodule.mkQ
    (fun _ _ => rfl) U.toSubmodule.mkQ_surjective A ho
  rw [Submodule.ker_mkQ, ← (subrepresentationFixedEquiv ρ U A).finrank_eq] at h
  exact h
end Representation.BinaryOffender
