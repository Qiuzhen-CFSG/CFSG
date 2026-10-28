module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeRankCubeFree
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order

/-!
# Quasithinness of six concrete Main Theorem models

The orders of A₅, A₆, A₈, M₁₁, M₂₂ and M₂₃ contain no odd prime cube.
The prime-rank order bound therefore proves strong quasithinness, and hence
quasithinness, of these actual carriers and their isomorphic copies.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2, printed p.4, repeated on p.482. These results establish only
the QT clause of the converse. The proper-K and even-characteristic clauses
remain separate obligations. A₉ is deliberately not treated by this method:
its ordinary 3-rank is three, though its 2-local odd ranks are at most two.
-/

namespace CFSG.Quasithin.MainConverse

open Sporadic.Mathieu

/-- Absence of odd prime cubes implies strong quasithinness. -/
public theorem stronglyQuasithin_of_odd_cube_not_dvd
    {G : Type*} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p → ¬ p ^ 3 ∣ Nat.card G) :
    IsStronglyQuasithin G := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact primeRank_le_two_of_cube_not_dvd (h p hp ho)

private theorem odd_cube_not_dvd_m23_order {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    ¬ p ^ 3 ∣ 10200960 := by
  intro hd
  have hpd : p ∣ Nat.card M23 := by
    rw [m23_order]
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rcases (m23_prime_dvd_order_iff p).mp hpd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  all_goals norm_num at hd

private theorem stronglyQuasithin_of_card_dvd_m23_order
    {G : Type*} [Group G] [Finite G] (hc : Nat.card G ∣ 10200960) :
    IsStronglyQuasithin G := by
  apply stronglyQuasithin_of_odd_cube_not_dvd
  intro p hp ho hd
  let : Fact p.Prime := ⟨hp⟩
  exact odd_cube_not_dvd_m23_order ho (hd.trans hc)

/-- The three alternating models whose orders have no odd prime cube. -/
public theorem alternating_stronglyQuasithin {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    IsStronglyQuasithin (alternatingGroup (Fin n)) := by
  apply stronglyQuasithin_of_card_dvd_m23_order
  rcases hn with rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

public theorem m11_stronglyQuasithin : IsStronglyQuasithin M11 :=
  stronglyQuasithin_of_card_dvd_m23_order (by rw [m11_order]; norm_num)

public theorem m22_stronglyQuasithin : IsStronglyQuasithin M22 :=
  stronglyQuasithin_of_card_dvd_m23_order (by rw [m22_order]; norm_num)

public theorem m23_stronglyQuasithin : IsStronglyQuasithin M23 :=
  stronglyQuasithin_of_card_dvd_m23_order (by rw [m23_order])

/-- Transport a proved concrete QT case to a model witness in any universe. -/
public theorem quasithin_of_model_equiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H) (hH : IsQuasithin H) : IsQuasithin G :=
  Theory.GroupTheory.isQuasithin_of_equiv e.symm hH

public theorem alternating_quasithin_of_iso {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : G ≃* alternatingGroup (Fin n)) : IsQuasithin G :=
  quasithin_of_model_equiv e (alternating_stronglyQuasithin hn).quasithin

public theorem m11_quasithin_of_iso {G : Type*} [Group G] [Finite G]
    (e : G ≃* M11) : IsQuasithin G :=
  quasithin_of_model_equiv e m11_stronglyQuasithin.quasithin

public theorem m22_quasithin_of_iso {G : Type*} [Group G] [Finite G]
    (e : G ≃* M22) : IsQuasithin G :=
  quasithin_of_model_equiv e m22_stronglyQuasithin.quasithin

public theorem m23_quasithin_of_iso {G : Type*} [Group G] [Finite G]
    (e : G ≃* M23) : IsQuasithin G :=
  quasithin_of_model_equiv e m23_stronglyQuasithin.quasithin

end CFSG.Quasithin.MainConverse
