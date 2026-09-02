module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Prime.Basic

namespace Theory.GroupAction

variable {G : Type*} [Group G]

/-! A small generic criterion used by the odd-order representation results. -/

/-! If every prime-order element of a finite subgroup has order `p`, then it is a `p`-group. -/
public theorem isPGroup_of_prime_order_eq_p [Finite G]
    (p : ℕ) [Fact p.Prime] (H : Subgroup G)
    (hprime : ∀ x : H, Nat.Prime (orderOf x) → orderOf x = p) :
    IsPGroup p H := by
  refine (IsPGroup.iff_orderOf (p := p) (G := H)).2 ?_
  intro x
  refine ⟨(Nat.primeFactorsList (orderOf x)).length, ?_⟩
  have h0 : orderOf x ≠ 0 := (Nat.pos_iff_ne_zero.mp (orderOf_pos x))
  exact Nat.eq_prime_pow_of_unique_prime_dvd h0 (by
    intro q hq hqd
    have hqd_card : q ∣ Nat.card (Subgroup.zpowers x) := by
      simpa [Nat.card_zpowers] using hqd
    letI : Fintype (Subgroup.zpowers x) := Fintype.ofFinite (Subgroup.zpowers x)
    have hqd_card' : q ∣ Fintype.card (Subgroup.zpowers x) := by
      simpa [Nat.card_eq_fintype_card] using hqd_card
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨y, hy⟩ :=
      _root_.exists_prime_orderOf_dvd_card (G := Subgroup.zpowers x) q hqd_card'
    have hy' : Nat.Prime (orderOf (y : H)) := by
      simpa [Subgroup.orderOf_coe, hy] using hq
    have hqy : orderOf (y : H) = p := hprime (y : H) hy'
    have hyq' : orderOf (y : H) = q := by
      simpa [Subgroup.orderOf_coe] using hy
    exact hyq'.symm.trans hqy)

end Theory.GroupAction
