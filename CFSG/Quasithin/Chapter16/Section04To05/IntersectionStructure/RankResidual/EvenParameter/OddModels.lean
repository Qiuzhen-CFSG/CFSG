module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import GorensteinWalter.PSL2CoprimeSylowCyclic

/-!
# Excluding the prime-field degree-two branch of E2

Every Sylow three-subgroup of PSL₂(p), for p prime, is cyclic. For p ≥ 7,
the defining characteristic differs from three and the torus calculation
applies. For p = 2, 3, 5, the actual order is not divisible by nine.
Thus the source hypothesis m₃(L) > 1 excludes this whole E2 branch,
without any Fermat–Mersenne restriction or assumption on automorphisms.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E2(ii),
p.1170, and Lemma 16.4.5, p.1184; Huppert II.8.2–5.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.EvenParameter
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups GorensteinWalter
open scoped MatrixGroups

private theorem psl_two_card_mul {S : Type*} [Group S] {q : ℕ}
    (h : ClassicalGroup.IsPSL S 2 q) :
    Nat.card S * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hq : 1 < q := hF ▸ (Finite.one_lt_card (α := F))
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hc
  have hsub : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  rw [hsub] at hc
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  calc
    _ = (q ^ 2 - 1) * (q * (q - 1)) := hc
    _ = _ := by ring

/-- Prime-field PSL₂ has cyclic Sylow three-subgroups and three-rank at most one. -/
theorem prime_psl_two_threeRank_le_one {L : Type*} [Group L] [Finite L]
    {p : ℕ} (hp : p.Prime) (hm : ClassicalGroup.IsPSL L 2 p) :
    primeRank 3 L ≤ 1 := by
  by_cases hp7 : 7 ≤ p
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    rw [primeRank_equiv 3 e]
    let _ : Fact p.Prime := ⟨hp⟩
    let P : Sylow 3 (PSL2MatrixGroup F) := default
    apply P.primeRank_le_one_of_isCyclic
    exact psl2_sylow_isCyclic_of_coprime_field_card F
      (p := p) (f := 1) (by simpa using hF) (hF ▸ hp7) 3 (by decide)
      (by rw [hF]; exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)) P
  · have hnine : ¬ 3 ^ 2 ∣ Nat.card L := by
      have ho := psl_two_card_mul hm
      have hp2 := hp.two_le
      have hcases : p = 2 ∨ p = 3 ∨ p = 5 := by
        have hp4 := hp.ne_one
        have hn4 : p ≠ 4 := by rintro rfl; norm_num at hp
        have hn6 : p ≠ 6 := by rintro rfl; norm_num at hp
        omega
      rcases hcases with rfl | rfl | rfl
      all_goals norm_num at ho
      all_goals omega
    let P : Sylow 3 L := default
    apply P.primeRank_le_one_of_isCyclic
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hn1 : n ≤ 1 := by
      by_contra hn1
      exact hnine ((hn ▸ pow_dvd_pow 3 (show 2 ≤ n by omega)).trans
        (P : Subgroup L).card_subgroup_dvd_card)
    apply isCyclic_of_card_dvd_prime (p := 3)
    rw [hn]
    simpa only [pow_one] using pow_dvd_pow 3 hn1

end CFSG.Quasithin.Chapter16.Intersections.EvenParameter
