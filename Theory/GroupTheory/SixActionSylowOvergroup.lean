module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index

/-!
# Subgroups containing a Sylow subgroup in a group with a small action

If a finite group acts on a group of order six with a two-group kernel,
a subgroup containing a Sylow two-subgroup is either a two-group or the
whole group. The Sylow index divides three, so there is no intermediate
subgroup with an odd part. This supplies normalizer equality in
Aschbacher--Smith 2.5.12, printed pp.557--558.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G A : Type*} [Group G] [Finite G] [Group A]

/-- An overgroup of the Sylow with an odd part is the whole group. -/
theorem eq_top_of_sylow_le_of_six_action
    (P : Sylow 2 G) (L : Subgroup G) (hPL : (P : Subgroup G) ≤ L)
    (hL : ¬ IsPGroup 2 L) (f : G →* A) (hf : IsPGroup 2 f.ker)
    (hA : Nat.card A = 6) : L = ⊤ := by
  have hkP : f.ker ≤ P := hf.le_sylow_of_normal P
  have hd : (P : Subgroup G).index ∣ 6 := by
    have hh := (index_dvd_of_le hkP).trans (show f.ker.index ∣ Nat.card A by
      rw [index_ker]
      exact card_subgroup_dvd_card f.range)
    rwa [hA] at hh
  have hPn : ¬ 2 ∣ (P : Subgroup G).index := P.not_dvd_index
  have hPi : (P : Subgroup G).index = 1 ∨ (P : Subgroup G).index = 3 := by
    have hh : (P : Subgroup G).index ∣ 3 := by
      exact (Nat.Coprime.dvd_mul_right (Nat.coprime_comm.mpr
        ((Nat.prime_two.coprime_iff_not_dvd).mpr hPn))).mp hd
    exact (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hh
  have hLi : L.index ∣ 3 := by
    rcases hPi with h1 | h3
    · have hPt : (P : Subgroup G) = ⊤ := index_eq_one.mp h1
      have hLt : L = ⊤ := top_unique (hPt ▸ hPL)
      rw [hLt, index_top]
      exact one_dvd _
    · exact h3 ▸ index_dvd_of_le hPL
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hLi with h1 | h3
  · exact index_eq_one.mp h1
  · have hPi3 : (P : Subgroup G).index = 3 := by
      rcases hPi with h1 | h3'
      · have hh := index_dvd_of_le hPL
        rw [h1, h3] at hh
        norm_num at hh
      · exact h3'
    have hrel : (P : Subgroup G).relIndex L = 1 := by
      have hh := relIndex_mul_index hPL
      rw [h3, hPi3] at hh
      omega
    have heq : (P : Subgroup G) = L := le_antisymm hPL (relIndex_eq_one.mp hrel)
    exact (hL (heq ▸ P.isPGroup')).elim
end Theory.GroupTheory
