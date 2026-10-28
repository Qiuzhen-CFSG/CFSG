module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.PermutationChecks
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# Fixed generators and relations for the Held outer centralizer

The involution inverts `twist`. Its checked 21st-power relation makes the
Bray word fixed. The checked relations for that word give a (5,7,6) pair
inside the fixed subgroup. An additional commuting relation separates this
pair's closure from the fixed element `a`.

All permutation checks use the actual Held carrier and its proved four-point
base. The fast Bray table has already been identified on all 2058 letters.
Source: GLS3 Table 5.3p, outer 2C row; ATLAS HeG1-p2058B0.
-/

public section
namespace Held.OuterInvolution.FixedStructure

private theorem involutive_of_sq {G : Type*} [Group G] (f : MulAut G) (hf : f ^ 2 = 1) :
    Function.Involutive f := by
  intro g
  have h := congrArg (fun e : MulAut G => e g) hf
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h

theorem action_involutive : Function.Involutive action := involutive_of_sq action action_sq

theorem representation_action (g : He) : representation (action g) =
    implementer ^ 5 * representation g * (implementer ^ 5)⁻¹ := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem twist_pow : twist ^ 21 = 1 := by
  apply Held.eq_of_four_point_images
  decide +kernel

theorem twist_inverted : action twist = twist⁻¹ := by
  simp only [twist, map_mul, map_inv, action_involutive _, mul_inv_rev, inv_inv]

/-- The Bray word belongs to the literal fixed subgroup. -/
theorem bray_fixed : action bray = bray := by
  have htw : twist ^ 11 * twist ^ 10 = 1 := by
    rw [← pow_add]
    exact twist_pow
  have hpow : (twist⁻¹) ^ 10 = twist ^ 11 := by
    rw [inv_pow]
    exact (eq_inv_of_mul_eq_one_left htw).symm
  have hg : b ^ 3 = action (b ^ 3) * twist := by simp [twist]
  simp only [bray, map_mul, map_pow, twist_inverted, hpow]
  conv_rhs => rw [hg, mul_assoc, ← pow_succ', map_pow]

theorem a_fixed : action a = a := by
  apply representation_injective
  rw [representation_action]
  change (implementer ^ 5) * atlasA * (implementer ^ 5)⁻¹ = atlasA
  have h : Commute implementer atlasA := mul_inv_eq_iff_eq_mul.mp conj_a
  exact mul_inv_eq_iff_eq_mul.mpr (h.pow_left 5).eq

set_option maxRecDepth 4096 in
theorem bray_pow_ten : bray ^ 10 = 1 := by
  apply Held.eq_of_four_point_images
  simp only [map_pow, map_one, bray_representation]
  decide +kernel

set_option maxRecDepth 4096 in
theorem a_bray_pow_twenty_one : (a * bray) ^ 21 = 1 := by
  apply Held.eq_of_four_point_images
  simp only [map_pow, map_mul, map_one, bray_representation]
  decide +kernel

set_option maxRecDepth 4096 in
theorem pair_product_pow_six : (bray ^ 2 * (a * bray) ^ 12) ^ 6 = 1 := by
  apply Held.eq_of_four_point_images
  simp only [map_pow, map_mul, map_one, bray_representation]
  decide +kernel

set_option maxRecDepth 4096 in
theorem first_commutes_center_word : Commute (bray ^ 2) ((a * bray) ^ 7) := by
  change bray ^ 2 * (a * bray) ^ 7 = (a * bray) ^ 7 * bray ^ 2
  apply Held.eq_of_four_point_images
  simp only [map_pow, map_mul, bray_representation]
  decide +kernel

set_option maxRecDepth 4096 in
/-- A word in the perfect pair giving the central element of order three. -/
theorem center_word_eq : (a * bray) ^ 7 =
    ((bray ^ 2)⁻¹ * ((a * bray) ^ 12)⁻¹) ^ 2 := by
  apply Held.eq_of_four_point_images
  simp only [map_pow, map_mul, map_inv, bray_representation]
  decide +kernel

/-- The fixed element `a` does not centralize the word centralized by the pair. -/
theorem a_not_commutes_center_word : ¬ Commute a ((a * bray) ^ 7) := by
  have hn : (atlasA * (atlasA * brayPermutation) ^ 7) (0 : Fin 2058) ≠
      ((atlasA * brayPermutation) ^ 7 * atlasA) 0 := by decide +kernel
  intro h
  have he := congrArg (fun g : He => representation g 0) h.eq
  simp only [map_mul, map_pow, bray_representation] at he
  exact hn he

end Held.OuterInvolution.FixedStructure
