module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Group

/-!
# Commutator images in a linear quotient layer

Let a subgroup act by conjugation on a group with a surjective additive
coordinate map. If conjugation descends to linear maps, the image of its
commutator subgroup is closed under scalars. Lift a scalar multiple of each
input before taking its commutator, and use a subgroup preimage to pass from
generators to arbitrary commutator products.

Consequently an elementary-normal-subgroup calculation on the original group
can force the acting subgroup to fix the whole layer. The root calculation is
an explicit hypothesis of the second theorem, not an assumed action kernel.
This is general group and module algebra used for the central triality
parabolic; it uses the convention [r,x] = r*x*r⁻¹*x⁻¹.
-/

public section

open Subgroup
open scoped commutatorElement

namespace Subgroup

variable {G F V : Type*} [Group G] [Ring F] [AddCommGroup V] [Module F V]

/-- Scalar multiples of a commutator image are again commutator images when
conjugation descends linearly to a surjective additive layer. -/
theorem commutator_layer_smul_closed
    (R X : Subgroup G) (u : R → V)
    (hu : ∀ r s, u (r * s) = u r + u s) (hsurj : Function.Surjective u)
    (ρ : X → MulAut R) (hρ : ∀ g r, (ρ g r).val = g.val * r.val * g.val⁻¹)
    (A : X → V →ₗ[F] V) (hA : ∀ g r, u (ρ g r) = A g (u r))
    (c : F) (r : R) (hr : r ∈ (⁅R, X⁆).subgroupOf R) :
    ∃ s ∈ (⁅R, X⁆).subgroupOf R, u s = c • u r := by
  have hu1 : u 1 = 0 := by
    have h := hu 1 1
    exact add_left_cancel (show u 1 + u 1 = u 1 + 0 by simpa using h.symm)
  have hui (t : R) : u t⁻¹ = -u t := by
    apply eq_neg_of_add_eq_zero_left
    rw [← hu, inv_mul_cancel, hu1]
  let N := (⁅R, X⁆).subgroupOf R
  let S : Subgroup R := {
    carrier := {r | ∃ s ∈ N, u s = c • u r}
    one_mem' := ⟨1, N.one_mem, by rw [hu1, smul_zero]⟩
    mul_mem' := by
      rintro a b ⟨s, hs, he⟩ ⟨t, ht, hf⟩
      exact ⟨s * t, N.mul_mem hs ht, by rw [hu, hu, he, hf, smul_add]⟩
    inv_mem' := by
      rintro a ⟨s, hs, he⟩
      exact ⟨s⁻¹, N.inv_mem hs, by rw [hui, hui, he, smul_neg]⟩ }
  have hval (a : R) (x : X) :
      ((a * (ρ x a)⁻¹ : R) : G) = ⁅a.val, x.val⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ, commutatorElement_def]
    group
  have hcomm : ⁅R, X⁆ ≤ S.map R.subtype := by
    apply commutator_le.mpr
    intro a ha x hx
    let r : R := ⟨a, ha⟩
    let y : X := ⟨x, hx⟩
    obtain ⟨t, ht⟩ := hsurj (c • u r)
    refine ⟨r * (ρ y r)⁻¹, ?_, hval r y⟩
    refine ⟨t * (ρ y t)⁻¹, ?_, ?_⟩
    · change ((t * (ρ y t)⁻¹ : R) : G) ∈ ⁅R, X⁆
      rw [hval]
      exact commutator_mem_commutator t.property hx
    · rw [hu, hu, hui, hui, hA, hA, ht, map_smul, smul_add, smul_neg]
  obtain ⟨s, hs, he⟩ := hcomm hr
  have he' : s = r := Subtype.ext he
  subst s
  exact hs

/-- A normal square-trivial commutator has zero image in a linear layer
whenever the root calculation excludes scalar-stable elementary images. -/
theorem action_layer_trivial_of_commutator_squares
    (R X : Subgroup G) (u : R → V)
    (hu : ∀ r s, u (r * s) = u r + u s) (hsurj : Function.Surjective u)
    (ρ : X → MulAut R) (hρ : ∀ g r, (ρ g r).val = g.val * r.val * g.val⁻¹)
    (A : X → V →ₗ[F] V) (hA : ∀ g r, u (ρ g r) = A g (u r))
    (hvanish : ∀ N : Subgroup R, N.Normal →
      (∀ n ∈ N, (n : R) ^ 2 = 1) →
      (∀ c : F, ∀ r ∈ N, ∃ s ∈ N, u s = c • u r) →
      ∀ r ∈ N, u r = 0)
    (hsq : ∀ z ∈ ⁅R, X⁆, (z : G) ^ 2 = 1)
    (x : X) (r : R) : u (ρ x r) = u r := by
  let N := (⁅R, X⁆).subgroupOf R
  have hN : N.Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left R X)
  have hzero := hvanish N hN
    (fun n hn => Subtype.ext (hsq n.val hn))
    (commutator_layer_smul_closed R X u hu hsurj ρ hρ A hA)
  have hu1 : u 1 = 0 := by
    have h := hu 1 1
    exact add_left_cancel (show u 1 + u 1 = u 1 + 0 by simpa using h.symm)
  have hui (t : R) : u t⁻¹ = -u t := by
    apply eq_neg_of_add_eq_zero_left
    rw [← hu, inv_mul_cancel, hu1]
  have hn : r * (ρ x r)⁻¹ ∈ N := by
    have he : ((r * (ρ x r)⁻¹ : R) : G) = ⁅r.val, x.val⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ, commutatorElement_def]
      group
    change ((r * (ρ x r)⁻¹ : R) : G) ∈ ⁅R, X⁆
    rw [he]
    exact commutator_mem_commutator r.property x.property
  apply (sub_eq_zero.mp ?_).symm
  simpa only [sub_eq_add_neg, hu, hui] using hzero _ hn

end Subgroup
