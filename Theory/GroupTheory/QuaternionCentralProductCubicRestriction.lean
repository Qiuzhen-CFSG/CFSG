module

public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Theory.GroupTheory.QuaternionElementaryEightCentralizer

/-!
# Faithful cubic restriction to an elementary eight

Independent cubic actors on a quaternion central product act faithfully on
any elementary eight that they normalize. If an actor centralizes the eight,
the two factor coordinates of each element are fixed modulo the common
center. A nontrivial cubic action on a quaternion group has no noncentral
fixed coset. Thus a nontrivial action on one factor would put the entire
eight inside the other factor, which is impossible.

This isolates the faithfulness step in the intrinsic geometry supporting
Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Subgroup

private theorem cubic_factor_action_eq_one_of_centralizes_eight
    {G : Type*} [Group G] [Finite G] (B C U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUQ : U ≤ B ⊔ C)
    (a : G) (haC : a ∈ normalizer (C : Set G))
    (f : MulAut B) (hf : ∀ b : B, (f b : G) = a * b * a⁻¹)
    (hf3 : f ^ 3 = 1) (haU : a ∈ centralizer (U : Set G)) : f = 1 := by
  classical
  by_contra hne
  obtain ⟨eB⟩ := hB
  have hBCn : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hUC : U ≤ C := by
    intro u hu
    have hu' : u ∈ (B : Set G) * (C : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B C hBCn]
      exact hUQ hu
    obtain ⟨b, hb, c, hc, hbc⟩ := hu'
    change b * c = u at hbc
    have hfix : a * (b * c) * a⁻¹ = b * c := by
      rw [hbc, ← haU u hu, mul_inv_cancel_right]
    have hc' : a * c * a⁻¹ ∈ C := (mem_normalizer_iff.mp haC c).mp hc
    have heq : b⁻¹ * (a * b * a⁻¹) = c * (a * c * a⁻¹)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).mpr
      calc
        b⁻¹ * (a * b * a⁻¹) * (a * c * a⁻¹) = b⁻¹ * (a * (b * c) * a⁻¹) := by group
        _ = c := by rw [hfix, inv_mul_cancel_left]
    have hdiff : (⟨b, hb⟩ : B)⁻¹ * f ⟨b, hb⟩ ∈ center B := by
      have hI : b⁻¹ * (a * b * a⁻¹) ∈ B ⊓ C := by
        refine ⟨?_, ?_⟩
        · rw [← hf ⟨b, hb⟩]
          exact B.mul_mem (B.inv_mem hb) (f ⟨b, hb⟩).property
        · rw [heq]
          exact C.mul_mem hc (C.inv_mem hc')
      rw [intersection_eq_factor_center B C ⟨eB⟩ hinter hcomm] at hI
      obtain ⟨v, hv, hv'⟩ := hI
      change (v : G) = b⁻¹ * (a * b * a⁻¹) at hv'
      have hvB : v = (⟨b, hb⟩ : B)⁻¹ * f ⟨b, hb⟩ := by
        apply Subtype.ext
        simpa only [coe_mul, coe_inv, hf] using hv'
      exact hvB ▸ hv
    have hbZ := QuaternionGroup.mem_center_of_central_difference_of_cube_eq_one_ne_one_of_equiv
      eB f hf3 hne hdiff
    have hbI : b ∈ B ⊓ C := by
      rw [intersection_eq_factor_center B C ⟨eB⟩ hinter hcomm]
      exact ⟨⟨b, hb⟩, hbZ, rfl⟩
    rw [← hbc]
    exact C.mul_mem hbI.2 hc
  have hself := inf_centralizer_elementary_eight_of_quaternion_factors
    B C U ⟨eB⟩ hC hinter hcomm hU hUQ
  have hBU : B ≤ U := by
    rw [← hself]
    refine le_inf le_sup_left ?_
    intro b hb u hu
    exact (hcomm b hb u (hUC hu)).symm
  have hle := card_le_of_le (le_inf (le_refl B) (hBU.trans hUC))
  have hBcard : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hBcard, hinter] at hle
  omega

/-- An independent cubic actor centralizing an elementary eight is trivial.
No normalization hypothesis on the elementary eight is needed here. -/
public theorem QuaternionIndependentCubics.eq_one_of_centralizes_eight
    {G : Type*} [Group G] [Finite G] {B C : Subgroup G}
    (actors : QuaternionIndependentCubics B C) (U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUQ : U ≤ B ⊔ C)
    (a : actors.A) (ha : (a : G) ∈ centralizer (U : Set G)) : a = 1 := by
  have ha3 : a ^ 3 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    actors.elementary.exponent_dvd_p a
  have hf := cubic_factor_action_eq_one_of_centralizes_eight B C U hB hC hinter
    hcomm hU hUQ a (actors.normalizes_right a.property)
    (actors.actionB a) (actors.actionB_apply a)
    (by rw [← map_pow, ha3, map_one]) ha
  have hg := cubic_factor_action_eq_one_of_centralizes_eight C B U hC hB
    (by simpa only [inf_comm] using hinter)
    (fun c hc b hb => (hcomm b hb c hc).symm) hU
    (by simpa only [sup_comm] using hUQ) a (actors.normalizes_left a.property)
    (actors.actionC a) (actors.actionC_apply a)
    (by rw [← map_pow, ha3, map_one]) ha
  apply actors.faithful
  change (actors.actionB a, actors.actionC a) =
    (actors.actionB 1, actors.actionC 1)
  rw [hf, hg, map_one, map_one]

/-- A nonidentity independent cubic actor normalizing an elementary eight
induces an automorphism of order three on it. -/
public theorem QuaternionIndependentCubics.orderOf_restriction_eq_three
    {G : Type*} [Group G] [Finite G] {B C : Subgroup G}
    (actors : QuaternionIndependentCubics B C) (U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUQ : U ≤ B ⊔ C)
    (a : actors.A) (ha : a ≠ 1) (haU : (a : G) ∈ normalizer (U : Set G)) :
    orderOf (U.normalizerMonoidHom ⟨a, haU⟩) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : (⟨(a : G), haU⟩ : normalizer (U : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    exact congrArg (fun x : actors.A => (x : G))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp actors.elementary.exponent_dvd_p a)
  apply orderOf_eq_prime (by rw [← map_pow, ha3, map_one])
  intro h
  apply ha
  apply actors.eq_one_of_centralizes_eight U hB hC hinter hcomm hU hUQ a
  have hk : (⟨(a : G), haU⟩ : normalizer (U : Set G)) ∈ U.normalizerMonoidHom.ker := h
  rw [normalizerMonoidHom_ker] at hk
  exact hk

end Subgroup
