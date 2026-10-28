module
public import Theory.GroupAction.OrderFifteenOnSixteen
public import Theory.GroupAction.BinaryCyclicInvolution

/-!
# No involution inverts an order-fifteen binary automorphism in dimension four

An automorphism of order fifteen on a group of order sixteen is regular on
nonidentity points. An inverting involution therefore fixes at most one such
point: two fixed points differ by a cyclic power whose square fixes a point,
and regularity and odd order force that power to be the identity. On an
elementary abelian two-group of order sixteen, rank-nullity and the inclusion
of the involution displacement in its fixed subgroup force at least four
fixed points, a contradiction.

This supplies the composite-order obstruction in Aschbacher--Smith,
*The Classification of Quasithin Groups*, D.2.11(2), printed p.183.
The regular-orbit input is proved in `OrderFifteenOnSixteen`.
-/

open scoped IsMulCommutative

namespace MulAut

/-- An involutory automorphism of a binary group of order sixteen cannot invert
an automorphism of order fifteen. -/
public theorem not_inverts_order_fifteen_on_sixteen
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (a b : MulAut V)
    (ha : orderOf a = 15) (hb : b ^ 2 = 1) :
    b * a * b⁻¹ ≠ a⁻¹ := by
  classical
  intro hinv
  have hbne : b ≠ 1 := by
    intro he
    have haa : a = a⁻¹ := by simpa [he] using hinv
    have hp : a ^ 2 = 1 := by simpa only [pow_two] using (inv_eq_iff_mul_eq_one.mp haa.symm)
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [ha] at hd
    norm_num at hd
  let C := FixedPoints.subgroup (Subgroup.zpowers b) V
  have huniq (v w : C) (hv : (v : V) ≠ 1) (hw : (w : V) ≠ 1) : v = w := by
    obtain ⟨n, hn⟩ := exists_zpow_apply_eq_of_order_fifteen hV a ha v w hv hw
    have hbv : b (v : V) = v := v.property ⟨b, Subgroup.mem_zpowers b⟩
    have hbw : b (w : V) = w := w.property ⟨b, Subgroup.mem_zpowers b⟩
    have hconj : b * a ^ n * b⁻¹ = (a ^ n)⁻¹ := by
      rw [← conj_zpow, hinv, inv_zpow]
    have heq : (a ^ n)⁻¹ (v : V) = w := by
      rw [← hconj]
      change b ((a ^ n) (b⁻¹ (v : V))) = w
      have hbinv : b⁻¹ (v : V) = v := by
        apply b.injective
        simpa using hbv.symm
      rw [hbinv, hn, hbw]
    have hsquare : ((a ^ n) ^ (2 : ℕ)) (v : V) = v := by
      change (a ^ n) ((a ^ n) (v : V)) = v
      rw [hn, ← heq]
      exact (a ^ n).apply_symm_apply v
    have hthree : orderOf (a ^ (3 : ℕ)) = 5 := by rw [orderOf_pow, ha]; decide
    have hs : (a ^ n) ^ (2 : ℕ) = 1 :=
      eq_one_of_commute_five_of_fixed hV (a ^ (3 : ℕ)) _ hthree
        (((Commute.refl a).pow_left 3).zpow_right n |>.pow_right 2) v hv hsquare
    have hd2 := orderOf_dvd_of_pow_eq_one hs
    have hd15 : orderOf (a ^ n) ∣ 15 := by
      rw [← ha]
      exact orderOf_dvd_of_mem_zpowers ⟨n, rfl⟩
    have ho : orderOf (a ^ n) = 1 := Nat.eq_one_of_dvd_one (by
      simpa using Nat.dvd_gcd hd2 hd15)
    have he : a ^ n = 1 := orderOf_eq_one_iff.mp ho
    apply Subtype.ext
    simpa [he] using hn
  let f : C → Bool := fun v => decide ((v : V) = 1)
  have hf : Function.Injective f := by
    intro v w he
    have he' : (v : V) = 1 ↔ (w : V) = 1 := by simpa [f] using he
    by_cases hv : (v : V) = 1
    · have hw : (w : V) = 1 := he'.mp hv
      exact Subtype.ext (hv.trans hw.symm)
    · have hw : (w : V) ≠ 1 := fun hw => hv (he'.mpr hw)
      exact huniq v w hv hw
  have hC : Nat.card C ≤ 2 := by
    simpa using Nat.card_le_card_of_injective f hf
  have hcount := cyclicInvolution_card_eq_fixed_mul_commutator (V := V) b ⟨hbne, hb⟩
  have hle := Subgroup.card_le_of_le (cyclicInvolution_commutator_le_fixed (V := V) b hb)
  change Nat.card (commutatorAction (Subgroup.zpowers b) V) ≤ Nat.card C at hle
  change Nat.card V = Nat.card C * Nat.card (commutatorAction (Subgroup.zpowers b) V) at hcount
  rw [hV] at hcount
  nlinarith

end MulAut
