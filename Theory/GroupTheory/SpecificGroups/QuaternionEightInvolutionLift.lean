module
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut

/-!
# Involutory lifts of quaternion quotient automorphisms

An automorphism of a quaternion eight whose square acts trivially modulo the
center admits an inner correction with square one. The checked table ranges
over the two generator images and the eight possible correcting elements.
An isomorphism transports the conclusion to an actual quaternion subgroup.

This supplies the single-factor lift in the quaternion-product transvection
calculation of Aschbacher–Smith, printed p.546.
-/

namespace QuaternionGroup
private abbrev K := QuaternionGroup 2
private def liftMap (p : K × K) : K → K
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val

set_option maxRecDepth 10000 in
private theorem involution_lift_table : ∀ p : K × K,
    (∀ x y : K, liftMap p (x*y) = liftMap p x * liftMap p y) →
    (∀ x y : K, y * (x⁻¹ * liftMap p (liftMap p x)) =
      (x⁻¹ * liftMap p (liftMap p x)) * y) →
    ∃ z : K, ∀ x : K, z * liftMap p (z * liftMap p x * z⁻¹) * z⁻¹ = x := by
  decide

private theorem inner_central_difference_table : ∀ z x : K,
    ∀ y : K, y * (x⁻¹ * (z*x*z⁻¹)) = (x⁻¹ * (z*x*z⁻¹)) * y := by
  decide

/-- An involutory action on the quaternion central quotient has an involutory lift. -/
public theorem exists_involution_central_difference
    (a : MulAut (QuaternionGroup 2))
    (ha : ∀ x, x⁻¹ * a (a x) ∈ Subgroup.center (QuaternionGroup 2)) :
    ∃ b : MulAut (QuaternionGroup 2), b ^ 2 = 1 ∧
      ∀ x, (a x)⁻¹ * b x ∈ Subgroup.center (QuaternionGroup 2) := by
  let p : K × K := (a (QuaternionGroup.a 1), a (xa 0))
  have hp (x : K) : liftMap p x = a x := by
    cases x with
    | a i =>
      change (a (QuaternionGroup.a 1)) ^ i.val = a (QuaternionGroup.a i)
      rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
    | xa i =>
      change a (xa 0) * (a (QuaternionGroup.a 1)) ^ i.val = a (xa i)
      rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
  obtain ⟨z, hz⟩ := involution_lift_table p
    (by simp only [hp, map_mul, implies_true])
    (by intro x y; simpa only [hp] using Subgroup.mem_center_iff.mp (ha x) y)
  refine ⟨MulAut.conj z * a, ?_, ?_⟩
  · ext x
    simpa only [pow_two, MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply, hp] using hz x
  · intro x
    apply Subgroup.mem_center_iff.mpr
    exact inner_central_difference_table z (a x)

/-- Transport the involutory quaternion lift to an actual quaternion subgroup. -/
public theorem exists_involution_central_difference_of_equiv {G : Type*} [Group G]
    (model : G ≃* QuaternionGroup 2) (a : MulAut G)
    (ha : ∀ x, x⁻¹ * a (a x) ∈ Subgroup.center G) :
    ∃ b : MulAut G, b ^ 2 = 1 ∧ ∀ x, (a x)⁻¹ * b x ∈ Subgroup.center G := by
  let a' := MulAut.congr model a
  have ha' : ∀ x, x⁻¹ * a' (a' x) ∈ Subgroup.center (QuaternionGroup 2) := by
    intro x
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨v, rfl⟩ := model.surjective x
    obtain ⟨w, rfl⟩ := model.surjective y
    simpa [a', MulAut.congr_apply] using congrArg model (Subgroup.mem_center_iff.mp (ha v) w)
  obtain ⟨b, hb, hd⟩ := exists_involution_central_difference a' ha'
  refine ⟨MulAut.congr model.symm b, ?_, ?_⟩
  · rw [← map_pow, hb, map_one]
  · intro x
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply model.injective
    have h := Subgroup.mem_center_iff.mp (hd (model x)) (model y)
    simpa [a', MulAut.congr_apply] using h
end QuaternionGroup
