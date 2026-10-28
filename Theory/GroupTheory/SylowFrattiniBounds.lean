module
public import Theory.Frattini.OmegaProducts
public import Mathlib.GroupTheory.Sylow

/-!
# Elementary Sylow Frattini size bounds

Frattini quotients are preserved by group equivalences. A Sylow subgroup
whose ambient order has p-part at most p^n has order at most p^n, and so
does its Frattini quotient. These transport and Lagrange bounds support
the finite-model Sylow restriction in Aschbacher--Smith 4.4.10, p.621.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SylowFrattiniBounds

/-- A group equivalence preserves the order of its Frattini quotient. -/
theorem card_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ frattini A) = Nat.card (B ⧸ frattini B) := by
  exact Nat.card_congr (QuotientGroup.congr _ _ e (frattini_map_equiv e)).toEquiv

/-- The ambient prime part bounds every Sylow Frattini quotient. -/
theorem card_le_of_order_not_dvd {G : Type*} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] (P : Sylow p G) (hc : ¬ p ^ (n + 1) ∣ Nat.card G) :
    Nat.card (P ⧸ frattini P) ≤ p ^ n := by
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hn : k ≤ n := by
    by_contra! h
    exact hc ((pow_dvd_pow p (by omega : n + 1 ≤ k)).trans
      (hk ▸ (P : Subgroup G).card_subgroup_dvd_card))
  exact (Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (frattini P))).trans
    (hk ▸ Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn)

end Theory.GroupTheory.SylowFrattiniBounds
