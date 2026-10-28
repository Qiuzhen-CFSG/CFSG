module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Conjugate spans and small intersections

If P and K induce the same conjugations on A, and C_G(A) normalizes U,
then their conjugate spans of U agree. An element of K differs from an
element of P by an element of that centralizer. We also record that two
different order-two subgroups intersect trivially, without requiring the
ambient group to be finite.

These elementary facts implement the normalizer and point-displacement
arguments in Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, Lemma 12.8.9, pp.852–853.
-/

namespace Subgroup
variable {G : Type*} [Group G]

public theorem conjugateSpanBy_eq_of_action_image (A U P K : Subgroup G)
    (hPK : P ≤ K) (hCU : centralizer (A : Set G) ≤ normalizer (U : Set G))
    (himage : ∀ k ∈ K, ∃ p ∈ P, ∀ a ∈ A, k * a * k⁻¹ = p * a * p⁻¹) :
    conjugateSpanBy U K = conjugateSpanBy U P := by
  apply le_antisymm _ (conjugateSpanBy_mono le_rfl hPK)
  apply (closure_le _).mpr
  rintro x ⟨k, hk, u, hu, rfl⟩
  obtain ⟨p, hp, heq⟩ := himage k hk
  have hc : p⁻¹ * k ∈ centralizer (A : Set G) := by
    intro a ha
    have he := congrArg (fun x : G => p⁻¹ * x * p) (heq a ha)
    have he' : (p⁻¹ * k) * a * (p⁻¹ * k)⁻¹ = a := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one] using he
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hu' := (mem_normalizer_iff.mp (hCU hc) u).mp hu
  apply subset_closure
  refine ⟨p, hp, (p⁻¹ * k) * u * (p⁻¹ * k)⁻¹, hu', ?_⟩
  group

public theorem inf_eq_bot_of_card_two_of_ne (A B : Subgroup G)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  obtain ⟨b, _, hb⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
  apply eq_bot_iff.mpr
  intro x hx
  by_contra hnon
  have hx1 : x ≠ 1 := by simpa only [mem_bot] using hnon
  apply hne
  have hax : (⟨x, hx.1⟩ : A) = a := ha _ (fun h => hx1 (congrArg Subtype.val h))
  have hbx : (⟨x, hx.2⟩ : B) = b := hb _ (fun h => hx1 (congrArg Subtype.val h))
  ext y
  by_cases hy : y = 1
  · simp [hy]
  constructor
  · intro hyA
    have hya := ha (⟨y, hyA⟩ : A) (fun h => hy (congrArg Subtype.val h))
    have hyx : y = x := congrArg Subtype.val (hya.trans hax.symm)
    exact hyx ▸ hx.2
  · intro hyB
    have hyb := hb (⟨y, hyB⟩ : B) (fun h => hy (congrArg Subtype.val h))
    have hyx : y = x := congrArg Subtype.val (hyb.trans hbx.symm)
    exact hyx ▸ hx.1
end Subgroup

