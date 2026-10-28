module
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.GeneratorInvariance
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Actual Held odd-order and cyclic Sylow bounds

The proved orbital preservation and pair-stabilizer divisibility discharge
the earlier order-bound interface. Its odd part is 3³·5²·7³·17. Thus only
3, 5 and 7 require noncyclic Sylow calculations in a perfect central cover.
No ambient order or Sylow hypothesis is added.
Source: Aschbacher–Smith I.1.3, printed p.407; GLS III Table 5.3p.
-/
namespace Held.OddPrimary
open Subgroup PerfectCentralCovering

public theorem card_dvd : Nat.card He ∣ 2 ^ 12 * (3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17) :=
  OddOrderBound.card_dvd_of_graph_and_pair_bound
    NormalizerGraph.Orbital.held_le_preservingGroup
    (LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd
      NormalizerGraph.Orbital.held_le_preservingGroup)

public theorem not_dvd_index_of_card
    {p n : ℕ} (P : Subgroup He) (hc : Nat.card P = p ^ n)
    (hn : ¬p ^ (n + 1) ∣ 2 ^ 12 * (3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17)) :
    ¬p ∣ P.index := by
  intro hd
  apply hn
  apply dvd_trans _ card_dvd
  rw [← P.card_mul_index, hc, pow_succ]
  exact Nat.mul_dvd_mul_left _ hd

private theorem square_not_dvd_card_model {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ¬p ^ 2 ∣ Nat.card He := by
  intro h
  have hb := h.trans card_dvd
  have hd := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hb
  simp only [hp.dvd_mul] at hd
  rcases hd with h2 | (((h3 | h5) | h7) | h17)
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
      (hp.dvd_of_dvd_pow h5))
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp
      (hp.dvd_of_dvd_pow h7))
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)).mp h17
    subst p
    norm_num at hb

public theorem sylow_isCyclic_of_ne_two_three_five_seven {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (P : Sylow p He) : IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact square_not_dvd_card_model Fact.out hp2 hp3 hp5 hp7
      ((pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup He).card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle

public theorem not_dvd_card_kernel_of_ne_two_three_five_seven
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* He) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hp7 : p ≠ 7) : ¬p ∣ Nat.card f.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact not_dvd_card_kernel_of_isCyclic_sylow f hf hk
    (sylow_isCyclic_of_ne_two_three_five_seven hp2 hp3 hp5 hp7)

end Held.OddPrimary
