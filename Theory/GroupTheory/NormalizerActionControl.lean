module

public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Normalizer control from a full point-fixer action

If a subgroup realizes every relevant conjugation on A, an arbitrary
actor differs from one of its elements by an element of C_G(A).
For an order-two subgroup Z, every normalizer element fixes Z pointwise.
Consequently a subgroup realizing all automorphisms of A fixing Z,
together with control of C_G(A), controls N_G(Z) ∩ N_G(A).

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.5, printed p.916. The chapter uses A=V₃, Z=V₁ and P=L₁T.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Lift the action, then absorb its centralizing difference. -/
theorem le_of_conjugation_image_lifts (A P K M : Subgroup G)
    (hP : P ≤ M) (hC : centralizer (A : Set G) ≤ M)
    (himage : ∀ k ∈ K, ∃ p ∈ P, ∀ a ∈ A, k * a * k⁻¹ = p * a * p⁻¹) :
    K ≤ M := by
  intro k hk
  obtain ⟨p, hp, heq⟩ := himage k hk
  have hc : p⁻¹ * k ∈ centralizer (A : Set G) := by
    intro a ha
    have he := congrArg (fun x : G => p⁻¹ * x * p) (heq a ha)
    have he' : (p⁻¹ * k) * a * (p⁻¹ * k)⁻¹ = a := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one] using he
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  simpa only [mul_inv_cancel_left] using M.mul_mem (hP hp) (hC hc)

/-- Full point-fixer action bounds the intersection of the two ambient normalizers. -/
theorem normalizer_intersection_le_of_point_fixer_action (V₁ V₃ P M : Subgroup G)
    (hcard : Nat.card V₁ = 2)
    (hP : P ≤ M) (hC : centralizer (V₃ : Set G) ≤ M)
    (haction : ∀ a : MulAut V₃,
      (∀ v : V₃, v.val ∈ V₁ → a v = v) →
      ∃ p ∈ P, ∀ v : V₃, (a v).val = p * v.val * p⁻¹) :
    normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M := by
  apply le_of_conjugation_image_lifts V₃ P _ M hP hC
  intro k hk
  let a := V₃.normalizerMonoidHom ⟨k, hk.2⟩
  have hfix : ∀ v : V₃, v.val ∈ V₁ → a v = v := by
    intro v hv
    have hc : Nat.card (V₁.subgroupOf (normalizer (V₁ : Set G))) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe V₁.le_normalizer).toEquiv).trans hcard
    have hz := central_of_normal_card_two
      (V₁.subgroupOf (normalizer (V₁ : Set G))) hc
    have hvk := congrArg Subtype.val
      (mem_center_iff.mp (hz (show (⟨v.val, V₁.le_normalizer hv⟩ : normalizer (V₁ : Set G)) ∈
        V₁.subgroupOf (normalizer (V₁ : Set G)) from hv)) ⟨k, hk.1⟩)
    change k * v.val = v.val * k at hvk
    apply Subtype.ext
    change k * v.val * k⁻¹ = v.val
    rw [hvk, mul_inv_cancel_right]
  obtain ⟨p, hp, he⟩ := haction a hfix
  exact ⟨p, hp, fun v hv => he ⟨v, hv⟩⟩

end Subgroup

end
