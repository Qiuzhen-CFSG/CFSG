module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Subgroups of prescribed order through an element

Every element of a finite elementary abelian two-group lies in a subgroup
of any prescribed positive rank up to its rank. Extend the cyclic subgroup
of the element using the subgroup-extension form of Sylow’s first theorem.
This gives the generation argument for Aschbacher–Smith, B.2.3(1).
-/

open scoped IsMulCommutative

namespace IsElementaryAbelian
variable {G : Type*} [Group G] [Finite G]

public theorem exists_two_power_subgroup_mem (A : Subgroup G) [IsElementaryAbelian 2 A]
    {n : ℕ} (hn : 0 < n) (hcard : 2 ^ n ≤ Nat.card A) (x : G) (hx : x ∈ A) :
    ∃ B : Subgroup G, B ≤ A ∧ IsElementaryAbelian 2 B ∧
      Nat.card B = 2 ^ n ∧ x ∈ B := by
  let a : A := ⟨x, hx⟩
  have ha : a ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hp := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hnm : n ≤ m := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hm ▸ hcard)
  have hdvd : 2 ^ n ∣ Nat.card A := hm ▸ pow_dvd_pow 2 hnm
  have hord : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha
  obtain horder | horder := (Nat.dvd_prime Nat.prime_two).mp hord
  all_goals
    have hc : Nat.card (Subgroup.zpowers a) = 2 ^ (if orderOf a = 1 then 0 else 1) := by
      rw [Nat.card_zpowers, horder]
      norm_num
    have hk : (if orderOf a = 1 then 0 else 1) ≤ n := by split_ifs <;> omega
    obtain ⟨K, hK, hKa⟩ := Sylow.exists_subgroup_card_pow_prime_le 2 hdvd
      (Subgroup.zpowers a) hc hk
    let : IsElementaryAbelian 2 K :=
      { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun k => by
          apply Subtype.ext
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 A) k.val }
    refine ⟨K.map A.subtype, Subgroup.map_subtype_le K, IsElementaryAbelian.map A.subtype,
      ?_, ?_⟩
    · exact (Subgroup.card_map_of_injective A.subtype_injective).trans hK
    · exact ⟨a, hKa (Subgroup.mem_zpowers a), rfl⟩
end IsElementaryAbelian
