module

public import Theory.SpecificGroups.Tits.MinimumIndex.OddIndex
public import Theory.SpecificGroups.Tits.MinimumIndex.Candidates
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups
import Mathlib.Tactic.NormNum

/-!
# Minimum proper-subgroup index of the concrete Tits group

Every proper subgroup of the actual degree-1600 ATLAS carrier has index
at least 1600. The faithful degree-1600 action alone
supplies no lower bound. `OddIndex` proves the entire odd-index branch.

For the remaining branch, a divisor of 2^11 * 3^3 * 5^2 * 13 not divisible
by 64, 25, or 13 is at most 2^5 * 3^3 * 5 = 4320. Thus it suffices to
place proper even-index subgroups with large two-part in a parabolic,
and bound proper overgroups containing a Sylow five- or thirteen-subgroup.
The conditional reductions below separate coverage from order certification.
The final `atlas1600_subgroup_index_ge` discharges every input using the
proved coverage and order bounds for the literal subgroups of this carrier.

Source: the primary ATLAS Tits entry lists primitive degrees beginning at
1600 and the relevant candidate overgroups:
https://brauer.maths.qmul.ac.uk/Atlas/exc/TF42/.
No maximal-subgroup catalogue is assumed here. The coverage inputs are
proved on `Atlas1600Group` by subgroup arguments and kernel-checked finite
certificates. This module supplies the minimum-index premise of the Rudvalis stabilizer argument,
without importing Rudvalis.
-/

namespace Tits
open Subgroup ExceptionalParabolics

private theorem restricted_divisor_bound (n : ℕ) (hd : n ∣ 17971200)
    (h64 : ¬ 64 ∣ n) (h25 : ¬ 25 ∣ n) (h13 : ¬ 13 ∣ n) : n ≤ 4320 := by
  have hn : n ∣ 2048 * (27 * (25 * 13)) := hd
  obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp hn
  obtain ⟨c, d, hc, hdd, rfl⟩ := Nat.dvd_mul.mp hb
  obtain ⟨e, f, he, hf, rfl⟩ := Nat.dvd_mul.mp hdd
  have ha32 : a ≤ 32 := by
    have ha' : a ∣ 2 ^ 11 := ha
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha'
    have hk6 : k < 6 := by
      by_contra h
      apply h64
      apply dvd_mul_of_dvd_left
      exact pow_dvd_pow 2 (by omega : 6 ≤ k)
    exact Nat.pow_le_pow_right (by decide) (by omega : k ≤ 5)
  have hc27 : c ≤ 27 := Nat.le_of_dvd (by decide) hc
  have he5 : e ≤ 5 := by
    have he' : e ∣ 5 ^ 2 := he
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp he'
    have hk2 : k < 2 := by
      by_contra h
      apply h25
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left (pow_dvd_pow 5 (by omega : 2 ≤ k)) _) _) _
    exact Nat.pow_le_pow_right (by decide) (by omega : k ≤ 1)
  have hf1 : f = 1 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 13)).mp hf with h | h
    · exact h
    · subst f
      exact False.elim (h13 (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right (dvd_mul_left 13 e) c) a))
  rw [hf1, mul_one]
  exact Nat.mul_le_mul ha32 (Nat.mul_le_mul hc27 he5)

private theorem index_ge_of_card_le (L : Subgroup Atlas1600Group)
    (hc : Nat.card L ≤ 11232) : 1600 ≤ L.index := by
  by_contra h
  have hm := Nat.mul_le_mul hc (show L.index ≤ 1599 by omega)
  rw [L.card_mul_index, atlas1600Group_card] at hm
  norm_num at hm

/-- Without any of the three large prime parts, Lagrange's theorem bounds
the subgroup order by 4320. No properness assumption is needed. -/
public theorem atlas1600_subgroup_card_le_of_small_prime_parts
    (L : Subgroup Atlas1600Group)
    (h64 : ¬ 64 ∣ Nat.card L) (h25 : ¬ 25 ∣ Nat.card L) (h13 : ¬ 13 ∣ Nat.card L) :
    Nat.card L ≤ 4320 :=
  restricted_divisor_bound _
    (atlas1600Group_card ▸ L.card_subgroup_dvd_card) h64 h25 h13

/-- Three precise overgroup inputs suffice for the full index bound.
These separate the large-two-part placement from the five- and
thirteen-overgroup bounds. -/
public theorem atlas1600_subgroup_index_ge_of_overgroup_bounds
    (hlargeTwo : ∀ L : Subgroup Atlas1600Group, L ≠ ⊤ → 2 ∣ L.index →
      64 ∣ Nat.card L → ¬ 25 ∣ Nat.card L → ¬ 13 ∣ Nat.card L →
      ∃ g : Atlas1600Group,
        L.map (MulAut.conj g).toMonoidHom ≤ first ∨
        L.map (MulAut.conj g).toMonoidHom ≤ second)
    (hfive : ∀ L : Subgroup Atlas1600Group, L ≠ ⊤ → 25 ∣ Nat.card L →
      Nat.card L ≤ 7800)
    (hthirteen : ∀ L : Subgroup Atlas1600Group, L ≠ ⊤ → 13 ∣ Nat.card L →
      Nat.card L ≤ 11232)
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) : 1600 ≤ L.index := by
  by_cases heven : 2 ∣ L.index
  · apply index_ge_of_card_le
    by_cases h13 : 13 ∣ Nat.card L
    · exact hthirteen L hL h13
    · by_cases h25 : 25 ∣ Nat.card L
      · have hc := hfive L hL h25
        omega
      · by_cases h64 : 64 ∣ Nat.card L
        · obtain ⟨g, hg⟩ := hlargeTwo L hL heven h64 h25 h13
          have hc := atlas1600_subgroup_card_le_of_conjugate_parabolic L g hg
          omega
        · have hc := atlas1600_subgroup_card_le_of_small_prime_parts L h64 h25 h13
          omega
  · exact (by decide : 1600 ≤ 1755).trans
      (atlas1600_subgroup_index_ge_of_odd_index L hL heven)

private theorem card_le_of_conjugate_le {L K : Subgroup Atlas1600Group}
    (g : Atlas1600Group) (h : L.map (MulAut.conj g).toMonoidHom ≤ K) :
    Nat.card L ≤ Nat.card K := by
  have hc := Subgroup.card_le_of_le h
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hc

/-- Literal candidate coverage and their order certificates discharge the
odd-prime inputs of the index reduction. This keeps coverage independent of
order certification, while the final assembly must supply both. -/
public theorem atlas1600_subgroup_index_ge_of_candidate_coverage
    (hlargeTwo : ∀ L : Subgroup Atlas1600Group, L ≠ ⊤ → 2 ∣ L.index →
      64 ∣ Nat.card L → ¬ 25 ∣ Nat.card L → ¬ 13 ∣ Nat.card L →
      ∃ g : Atlas1600Group,
        L.map (MulAut.conj g).toMonoidHom ≤ first ∨
        L.map (MulAut.conj g).toMonoidHom ≤ second)
    (hfive : ∀ L : Subgroup Atlas1600Group, L ≠ ⊤ → 25 ∣ Nat.card L →
      ∃ g : Atlas1600Group,
        L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max4 ∨
        L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max8)
    (hthirteen : ∀ L : Subgroup Atlas1600Group, L ≠ ⊤ → 13 ∣ Nat.card L →
      ∃ g : Atlas1600Group,
        L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max1 ∨
        L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max2 ∨
        L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max4)
    (h1 : Nat.card MinimumIndexCandidates.max1 ≤ 11232)
    (h2 : Nat.card MinimumIndexCandidates.max2 ≤ 11232)
    (h4 : Nat.card MinimumIndexCandidates.max4 ≤ 7800)
    (h8 : Nat.card MinimumIndexCandidates.max8 ≤ 1200)
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) : 1600 ≤ L.index := by
  apply atlas1600_subgroup_index_ge_of_overgroup_bounds hlargeTwo ?_ ?_ L hL
  · intro K hK hd
    obtain ⟨g, hg⟩ := hfive K hK hd
    rcases hg with h | h
    · exact (card_le_of_conjugate_le g h).trans h4
    · exact ((card_le_of_conjugate_le g h).trans h8).trans (by decide)
  · intro K hK hd
    obtain ⟨g, hg⟩ := hthirteen K hK hd
    rcases hg with h | h | h
    · exact (card_le_of_conjugate_le g h).trans h1
    · exact (card_le_of_conjugate_le g h).trans h2
    · exact ((card_le_of_conjugate_le g h).trans h4).trans (by decide)

/-- Every proper subgroup of the concrete degree-1600 Tits carrier has
index at least 1600. All candidate coverage and order premises are discharged. -/
public theorem atlas1600_subgroup_index_ge
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) : 1600 ≤ L.index :=
  atlas1600_subgroup_index_ge_of_candidate_coverage
    MinimumIndex.LargeTwoOvergroups.large_two_subgroup_placement
    MinimumIndexFiveOvergroups.coverage MinimumIndexThirteen.coverage
    MinimumIndexCandidates.max1_card_le MinimumIndexCandidates.max2_card_le
    MinimumIndexCandidates.max4_card_le MinimumIndexCandidates.max8_card_le L hL

end Tits
