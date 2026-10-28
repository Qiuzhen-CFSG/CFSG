module

public import Mathlib.GroupTheory.PGroup

/-!
# Prime-order lifts and coprime kernels

A lift of an element of order p can be powered to a lift of order p when
its ambient finite group has no element of order p². The absence of p²
ensures that the powering exponent is coprime to p, so the image remains
nontrivial. This explicitly supplies the hypothesis missing from an
unrestricted assertion that prime-order elements lift with the same order.

A homomorphism with p-group kernel also preserves the order of every element
whose order is coprime to p. Both statements follow directly from the
order-of-a-power formula and Lagrange's theorem.
-/

/-- If a finite group has no element of order p², a nontrivial image of
order p has a lift of order p with nontrivial image. -/
public theorem MonoidHom.exists_prime_order_lift_of_no_prime_square_order
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) {p : ℕ} (hp : p.Prime)
    (hno : ∀ a : G, orderOf a ≠ p * p)
    (a : G) (ha : orderOf (f a) = p) :
    ∃ b : G, orderOf b = p ∧ orderOf (f b) = p := by
  have hd : p ∣ orderOf a := ha ▸ orderOf_map_dvd f a
  have hcop : p.Coprime (orderOf a / p) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    have hd2 : p * p ∣ orderOf a := (Nat.dvd_div_iff_mul_dvd hd).mp hdiv
    exact hno (a ^ (orderOf a / (p * p)))
      (orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos a)) hd2)
  refine ⟨a ^ (orderOf a / p), orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos a)) hd, ?_⟩
  rw [map_pow]
  exact (ha ▸ hcop : (orderOf (f a)).Coprime (orderOf a / p)).orderOf_pow.trans ha

/-- A homomorphism with p-group kernel preserves coprime element orders. -/
public theorem MonoidHom.orderOf_map_eq_of_coprime_of_isPGroup_ker
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) {p : ℕ} (hk : IsPGroup p f.ker)
    (a : G) (hcop : p.Coprime (orderOf a)) : orderOf (f a) = orderOf a := by
  apply Nat.dvd_antisymm (orderOf_map_dvd f a)
  apply orderOf_dvd_of_pow_eq_one
  let b : f.ker := ⟨a ^ orderOf (f a), by simp only [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]⟩
  have hd : orderOf b ∣ orderOf a := by
    rw [← Subgroup.orderOf_coe b]
    exact orderOf_pow_dvd _
  have hb : b = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hk.orderOf_coprime hcop b) dvd_rfl hd)
  exact congrArg Subtype.val hb
