module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import Theory.Mathieu.M12.Properties.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ThreeRank
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Odd-rank witnesses for the four enlargement alternatives

The alternating smaller components supply a three-rank lower bound directly
in the linear and Higman–Sims cases. In the Mathieu and Hall–Janko cases,
the concrete elementary nines lift through O₂(K), using the coprime-quotient
rank theorem. The smaller groups have order divisible by three, including
the actual projective matrix carrier PSL₃(2).

These are the intrinsic inputs to the nonfusion proof of Aschbacher–Smith,
16.3.10, combined manuscript of 1 March 2004, printed p.1181. No classification
or normality assertion is assumed beyond the stated four alternatives and
containment of the smaller component.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks
variable {G : Type*} [Group G] [Finite G] {K L : Subgroup G} {z : G}

private theorem three_dvd_alt_five : 3 ∣ Nat.card (alternatingGroup (Fin 5)) := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem three_dvd_alt_six : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem three_dvd_alt_eight : 3 ∣ Nat.card (alternatingGroup (Fin 8)) := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem three_dvd_psl_three_two :
    3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rw [← Nat.card_congr Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.toEquiv,
    Atlas.Comparisons.Exceptional.sl3Two_card]
  norm_num

private theorem rank_of_alternating {n : ℕ} (hn : 6 ≤ n) (hLK : L ≤ K)
    (he : Nonempty (L ≃* alternatingGroup (Fin n))) : 2 ≤ primeRank 3 K := by
  obtain ⟨e⟩ := he
  have hr : 2 ≤ primeRank 3 L := by
    rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank hn
  exact hr.trans (_root_.primeRank_le_of_injective 3 (inclusion hLK) (inclusion_injective hLK))

omit [Finite G] in
/-- Each of the four smaller components has order divisible by three. -/
theorem smaller_three_dvd (h : FourAlternatives K L z) : 3 ∣ Nat.card L := by
  rcases h with ⟨_, _, _, _, ⟨e⟩⟩ | ⟨_, h⟩
  · rw [Nat.card_congr e.toEquiv]
    exact three_dvd_alt_six
  · rcases h with ⟨_, ⟨e⟩⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · rw [Nat.card_congr e.toEquiv]
      exact three_dvd_alt_five
    · rcases h with h | h
      · obtain ⟨e⟩ := h
        rw [Nat.card_congr e.toEquiv]
        exact three_dvd_alt_five
      · obtain ⟨e⟩ := h
        rw [Nat.card_congr e.toEquiv]
        exact three_dvd_psl_three_two
    · rcases h with h | h
      · obtain ⟨e⟩ := h
        rw [Nat.card_congr e.toEquiv]
        exact three_dvd_alt_six
      · obtain ⟨e⟩ := h
        rw [Nat.card_congr e.toEquiv]
        exact three_dvd_alt_eight

/-- All four alternatives give an elementary odd-rank witness in K itself,
including when the model is only identified after quotienting by O₂(K). -/
theorem larger_three_rank (hLK : L ≤ K) (h : FourAlternatives K L z) :
    2 ≤ primeRank 3 K := by
  rcases h with ⟨_, _, _, _, hL⟩ | ⟨_, h⟩
  · exact rank_of_alternating (by decide) hLK hL
  · rcases h with ⟨⟨e⟩, _⟩ | ⟨⟨e⟩, _⟩ | ⟨_, hL⟩
    · change (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M12 at e
      have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
        rw [primeRank_congr 3 e]
        exact Sporadic.Mathieu.m12_three_rank_ge_two
      exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
    · change (K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier at e
      have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
        rw [primeRank_congr 3 e]
        exact Sporadic.LeechRelated.J2.three_rank_ge_two
      exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
    · rcases hL with hL | hL
      · exact rank_of_alternating (by decide) hLK hL
      · exact rank_of_alternating (by decide) hLK hL

/-- The two intrinsic inputs required by the distinct-component nonfusion argument. -/
theorem odd_rank_witnesses (hLK : L ≤ K) (h : FourAlternatives K L z) :
    2 ≤ primeRank 3 K ∧ 3 ∣ Nat.card L :=
  ⟨larger_three_rank hLK h, smaller_three_dvd h⟩

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks
