module
public import Theory.GroupTheory.SolvableSylowOvergroups.CentralCoverOrderActors
public import Theory.Mathieu.QuinticSylowActors

/-!
# Quintic actors on central covers of M₂₂

Descend the action on a normal perfect subgroup through its whole center.
The action retains precisely the original centralizer kernel. The native
M₂₂ Sylow-overgroup bound then excludes an order-five actor whose Sylow
join has order dividing a power of two times five.

Source: Aschbacher–Smith 5.1.13 and 5.2.2, printed pp.636–638,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.QuinticSylowActors
variable {G : Type*} [Group G] [Finite G]

/-- A central cover of M₂₂ admits no faithful quintic actor with the
original two-times-five Sylow-join order bound. -/
theorem no_five_actor_central_cover (K E : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* M22) (S : Sylow 2 G) {a : ℕ}
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  apply no_odd_actor_of_central_cover_sylow_order_bound K E e S (by decide : Odd 5)
    m22_center_eq_bot
    (IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [pow_one] using M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two))
    _ hE hd hc
  intro P J hJ hPJ
  have h3 : ¬3 ∣ Nat.card J := Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right (by decide)).of_dvd_right hJ)
  have h11 : ¬11 ∣ Nat.card J := (by decide : Nat.Prime 11).coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 11 2).pow_right a).mul_right (by decide)).of_dvd_right hJ)
  rw [M22QuinticSylow.card_eq_128 P J hPJ h3 h11]
  decide

end Sporadic.Mathieu.QuinticSylowActors
