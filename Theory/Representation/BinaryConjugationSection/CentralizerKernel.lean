module
public import Theory.Representation.BinaryConjugationSection
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Centralizer kernels on a literal binary section

The kernel of the action on U/Z contains C_H(U). For a subgroup A of H
normalized by U and disjoint from Z, it is exactly C_A(U): every
commutator killed by the section lies in both A and Z. A nontrivial
image of A therefore also forces A ∩ U to be nontrivial.

This uses relative normalization and the specified coordinate map;
neither A nor U is assumed normal in the ambient group. Source application:
Aschbacher–Smith, The Classification of Quasithin Groups, 13.8.32,
printed p.965, at the two ends of the same critical pair.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}
  (d : BinaryConjugationSection H U Z ρ)

include d

/-- An actor centralizing the whole section group lies in its action kernel. -/
theorem centralizer_le_of_action_kernel (Q : Subgroup G)
    (hker : ∀ h : H, (∀ w, ρ h w = w) ↔ (h : G) ∈ Q) :
    H ⊓ centralizer (U : Set G) ≤ Q := by
  intro x hx
  apply (hker ⟨x,hx.1⟩).mp
  intro w
  obtain ⟨u,hu⟩ := d.onto (Multiplicative.ofAdd w)
  have he : (⟨x * u * x⁻¹,
      (mem_normalizer_iff.mp (d.normalized hx.1) u).mp u.property⟩ : U) = u := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 u u.property).symm
  have hh := d.equivariant ⟨x,hx.1⟩ u
  rw [he,hu] at hh
  exact hh.symm

/-- Disjointness from the section denominator makes the action kernel the
actual centralizer on a mutually normalizing subgroup. -/
theorem inf_centralizer_eq_inf_action_kernel (Q A : Subgroup G)
    (hker : ∀ h : H, (∀ w, ρ h w = w) ↔ (h : G) ∈ Q)
    (hAH : A ≤ H) (hn : U ≤ normalizer (A : Set G))
    (hdisjoint : A ⊓ Z = ⊥) :
    A ⊓ centralizer (U : Set G) = A ⊓ Q := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1,d.centralizer_le_of_action_kernel Q hker ⟨hAH hx.1,hx.2⟩⟩
  · intro x hx
    refine ⟨hx.1,?_⟩
    intro u hu
    let uU : U := ⟨u,hu⟩
    let c : U := (⟨x * u * x⁻¹,
      (mem_normalizer_iff.mp (d.normalized (hAH hx.1)) u).mp hu⟩ : U) * uU⁻¹
    have hcZ : (c : G) ∈ Z := by
      apply (d.coordinates_eq_one_iff c).mp
      apply Multiplicative.toAdd.injective
      change (d.coordinates (_ * uU⁻¹)).toAdd = 0
      rw [map_mul,map_inv]
      change (d.coordinates _).toAdd + -(d.coordinates uU).toAdd = 0
      rw [d.equivariant ⟨x,hAH hx.1⟩ uU,
        (hker ⟨x,hAH hx.1⟩).mpr hx.2,add_neg_cancel]
    have hcA : (c : G) ∈ A :=
      (le_normalizer_iff_commutator_le_left.mp hn) (commutator_mem_commutator hx.1 hu)
    have hc : (c : G) = 1 := mem_bot.mp (hdisjoint ▸ (show (c:G) ∈ A ⊓ Z from ⟨hcA,hcZ⟩))
    change x * u * x⁻¹ * u⁻¹ = 1 at hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm

/-- A nontrivial quotient action forces a nontrivial intersection of the
two mutually normalizing subgroups. -/
theorem inf_ne_bot_of_action_kernel (Q A : Subgroup G)
    (hker : ∀ h : H, (∀ w, ρ h w = w) ↔ (h : G) ∈ Q)
    (hAH : A ≤ H) (hn : U ≤ normalizer (A : Set G))
    (houtside : ¬ A ≤ Q) : A ⊓ U ≠ ⊥ := by
  intro he
  have hc : ⁅A,U⁆ = ⊥ := bot_unique ((le_inf
    (le_normalizer_iff_commutator_le_left.mp hn)
    (le_normalizer_iff_commutator_le_right.mp (hAH.trans d.normalized))).trans_eq he)
  exact houtside ((le_inf hAH (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    (d.centralizer_le_of_action_kernel Q hker))

end Representation.BinaryConjugationSection
