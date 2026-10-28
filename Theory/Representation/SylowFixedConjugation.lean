module
public import Theory.Representation.BinaryOffender.Defs
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Fixed-space bounds for marked conjugation modules

Intersect a Sylow subgroup with its normalized component, then map that
Sylow through the actual surjective action map. An equivariant marking
embeds the ambient fixed subgroup into the model's Sylow fixed space.
For a commuting product U B with B fixed, multiplication also bounds the
fixed subgroup by |C_U(A)| |B|. These estimates control the central seed in
Aschbacher–Smith 13.4.10(5), printed p.909.
-/

public noncomputable section
open Subgroup Representation
open scoped Pointwise
universe u v w
variable {G : Type u} [Group G] [Finite G]

namespace Representation.BinaryOffender

/-- Transport a uniform model Sylow bound through the original conjugation action. -/
theorem sylow_fixed_card_le_of_conjugation_marking
    (T : Sylow 2 G) (K U : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    {Q : Type v} [Group Q] [Finite Q]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) Q W) (q : K →* Q) (hq : Function.Surjective q)
    (e : U ≃* Multiplicative W)
    (he : ∀ (k : K) (a : U),
      (e (U.normalizerMonoidHom ⟨k.val,hKU k.property⟩ a)).toAdd =
        ρ (q k) (e a).toAdd)
    (n : ℕ) (bound : ∀ P : Sylow 2 Q, Nat.card (fixedSpace ρ (P : Subgroup Q)) ≤ n) :
    Nat.card (U ⊓ centralizer (T : Set G) : Subgroup G) ≤ n := by
  let H := K ⊔ (T : Subgroup G)
  let X := K.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨R,hR⟩ := (T.subtype le_sup_right).exists_subgroupOf_eq_of_normal X
  let eK : X ≃* K := subgroupOfEquivOfLe (le_sup_left : K ≤ H)
  let P := R.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP : ∀ k ∈ (P : Subgroup K), (k : G) ∈ (T : Subgroup G) := by
    rintro k ⟨r,hr,rfl⟩
    rw [hR] at hr
    exact hr
  let S := P.mapSurjective hq
  let f : (U ⊓ centralizer (T : Set G) : Subgroup G) →
      fixedSpace ρ (S : Subgroup Q) := fun a =>
    ⟨(e ⟨a.val,a.property.1⟩).toAdd, by
      intro b
      obtain ⟨k,hk,hkb⟩ := b.property
      have ha : U.normalizerMonoidHom ⟨k.val,hKU k.property⟩
          ⟨a.val,a.property.1⟩ = ⟨a.val,a.property.1⟩ := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (a.property.2 k (hP k hk))
      have hh := he k ⟨a.val,a.property.1⟩
      rw [ha,hkb] at hh
      exact hh.symm⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : U => x.val)
      (e.injective (Multiplicative.toAdd.injective (congrArg Subtype.val hab))))
  exact (Nat.card_le_card_of_injective f hf).trans (bound S)

end Representation.BinaryOffender
namespace Subgroup

/-- A fixed commuting factor multiplies the fixed-space cardinality bound. -/
theorem card_fixed_sup_le_mul_of_centralizes
    (U A B : Subgroup G) (hBU : B ≤ centralizer (U : Set G))
    (hBA : B ≤ centralizer (A : Set G)) :
    Nat.card ((U ⊔ B) ⊓ centralizer (A : Set G) : Subgroup G) ≤
      Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) * Nat.card B := by
  let f : (U ⊓ centralizer (A : Set G) : Subgroup G) × B →
      ((U ⊔ B) ⊓ centralizer (A : Set G) : Subgroup G) := fun p =>
    ⟨p.1.val * p.2.val, mul_mem_sup p.1.property.1 p.2.property,
      (centralizer (A : Set G)).mul_mem p.1.property.2 (hBA p.2.property)⟩
  have hf : Function.Surjective f := by
    intro x
    have hx : x.val ∈ (U : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U B
        (hBU.trans (centralizer_le_normalizer (U : Set G)))]
      exact x.property.1
    obtain ⟨a,ha,b,hb,hab⟩ := hx
    have haC : a ∈ centralizer (A : Set G) := by
      have hh := (centralizer (A : Set G)).mul_mem x.property.2
        ((centralizer (A : Set G)).inv_mem (hBA hb))
      rwa [← hab, mul_inv_cancel_right] at hh
    exact ⟨(⟨a,ha,haC⟩,⟨b,hb⟩), Subtype.ext hab⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

end Subgroup
