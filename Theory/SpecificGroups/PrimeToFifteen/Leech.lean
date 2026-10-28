module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2.CentralizerSection.TwoKernel
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.Quotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.TwoKernel
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeRank.Elementary
public import Theory.SpecificGroups.PrimeToFifteen.Classical.LinearSymplectic
public import Theory.GroupTheory.PrimeRankZero

/-!
# Three-divisibility from the actual Leech-related local subgroups

The existing elementary three-subgroups of Co₂, McL and Suz, and the
constructed PSp₆(2) quotient of the Co₃ local subgroup, give a factor three
in each carrier order. Reusing these structural certificates avoids repeating
large kernel reductions in the original permutation actions.
Source: GLS3 Tables 5.3j–n and Aschbacher–Smith A.2.19.
-/

public section
namespace Theory.SpecificGroups.PrimeToFifteen
private theorem three_dvd_of_rank {G : Type*} [Group G] [Finite G]
    (h : 3 ≤ primeRank 3 G) : 3 ∣ Nat.card G := by
  by_contra hn
  have he := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
  omega

theorem co2 : 3 ∣ Nat.card Sporadic.LeechRelated.Co2.Carrier :=
  (three_dvd_of_rank
    Sporadic.LeechRelated.Co2.CentralizerSection.ThreeRank.three_le_primeRank_numerator).trans
      Sporadic.LeechRelated.Co2.CentralizerSection.numerator.card_subgroup_dvd_card

theorem suz : 3 ∣ Nat.card Sporadic.LeechRelated.Suz.Carrier :=
  (three_dvd_of_rank
    Sporadic.LeechRelated.Suz.CentralizerSection.numerator_primeRank_three_ge).trans
      Sporadic.LeechRelated.Suz.CentralizerSection.numerator.card_subgroup_dvd_card

theorem mcl : 3 ∣ Nat.card Sporadic.LeechRelated.McL.Carrier :=
  three_dvd_of_rank (by have h := Sporadic.LeechRelated.McL.four_le_primeRank_three; omega)

theorem co3 : 3 ∣ Nat.card Sporadic.LeechRelated.Co3.Carrier := by
  have hd : 3 ∣ Nat.card Sporadic.LeechRelated.Co3.CentralizerSection.SymplecticQuotient :=
    Classical.symplectic_three_dvd (ZMod 2) (by decide : 1 ≤ 3)
  exact hd.trans ((Subgroup.card_dvd_of_surjective
    Sporadic.LeechRelated.Co3.CentralizerSection.quotientMap
    Sporadic.LeechRelated.Co3.CentralizerSection.quotientMap_surjective).trans
      Sporadic.LeechRelated.Co3.CentralizerSection.numerator.card_subgroup_dvd_card)
end Theory.SpecificGroups.PrimeToFifteen
