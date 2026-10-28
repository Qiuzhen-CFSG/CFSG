module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Rank reduction for generation bounds

The rank of the actor image in either intrinsic E-member quotient is at
most the rank of its elementary abelian source, hence at most m₂(G).
Consequently every established generation bound reduces to m₂(G).
Cauchy supplies positivity of that rank in even order. The minimum bound
retains an explicit existence premise: general existence is not inferred
from the natural infimum of an empty set.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, E.1.7 and E.1.11--13, pp.210--214.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- Every E-member already satisfies the ambient two-rank bound. -/
theorem IsEMember.at_primeRank {T A K : Subgroup G} (h : IsEMember T A K) :
    IsEMemberAt (primeRank 2 G) T A K := by
  let _ := h.1
  have hAK : A ≤ K := h.2.2.1
  have hAr : Group.rank (A.subgroupOf K) ≤ primeRank 2 G := by
    rw [Group.rank_congr (subgroupOfEquivOfLe hAK)]
    exact A.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 A)
  have hr (N : Subgroup K) [N.Normal] :
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤ primeRank 2 G :=
    (Group.rank_le_of_surjective ((QuotientGroup.mk' N).subgroupMap _)
      ((QuotientGroup.mk' N).subgroupMap_surjective _)).trans hAr
  refine ⟨h, ?_⟩
  rcases h.2.2.2.2.2 with ho | hc
  · exact Or.inl ⟨ho, hr _⟩
  · exact Or.inr ⟨hc, hr _⟩

/-- Once generation is established, its rank bound can be reduced to `m₂(G)`.
This theorem does not infer existence from an empty natural infimum. -/
theorem IsEGenerated.at_primeRank {i : ℕ} (h : IsEGenerated i G) :
    IsEGenerated (primeRank 2 G) G := by
  intro T Ω hΩ
  apply top_unique
  rw [← h T Ω hΩ]
  apply sup_le_sup_right
  apply iSup_mono
  intro A
  apply sSup_le_sSup
  intro K hK
  exact hK.1.at_primeRank

/-- The two-rank is positive for an even-order finite group. -/
theorem primeRank_two_pos_of_even (heven : ¬ Odd (Nat.card G)) : 0 < primeRank 2 G := by
  have hd : 2 ∣ Nat.card G := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp heven)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hd
  have hne : g ≠ 1 := by intro h; simp [h] at hg
  let _ : Nontrivial (zpowers g) := (nontrivial_iff_ne_bot _).mpr (zpowers_ne_bot.mpr hne)
  have hp : IsPGroup 2 (zpowers g) := IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers, hg, pow_one])
  exact (Group.rank_pos (zpowers g)).trans_le ((zpowers g).rank_le_primeRank 2 hp)

/-- E.1.7's numerical step, given an actual positive generation witness. -/
theorem generationParameter_le_primeRank_of_exists
    (hex : ∃ i : ℕ, 0 < i ∧ IsEGenerated i G) : generationParameter G ≤ primeRank 2 G := by
  by_cases ho : Odd (Nat.card G)
  · rw [generationParameter_eq_zero_of_odd ho]
    exact Nat.zero_le _
  obtain ⟨i, _, hi⟩ := hex
  exact generationParameter_le (primeRank_two_pos_of_even ho) hi.at_primeRank


end CFSG.Quasithin.ChapterE
