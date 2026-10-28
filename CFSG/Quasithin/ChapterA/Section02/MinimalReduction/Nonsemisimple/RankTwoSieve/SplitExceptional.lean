module
public import Theory.SpecificGroups.LieType.TwoRankLower.BinaryExceptional
public import Theory.SpecificGroups.LieType.TwoRankLower.OddExceptional
public import CFSG.KnownSimple.ExceptionalModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
/-!
# The complete E6, E7 and E8 source exclusions in the rank-two sieve

Characteristic two uses the actual Sp6(2) embeddings. Every odd characteristic
uses the independent sign-coroot actors on the faithful root chart. Thus all
parameters of these three full catalogue entries are excluded for the literal
source quotient S/Z(S), without a quotient-quasithinness hypothesis.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- Every literal E6 model is absent from the ordinary two-rank-two list. -/
theorem no_e6_model (hr : primeRank 2 Q ≤ 2) {q : ℕ}
    (model : ExceptionalGroup.IsE6 Q q) : False := by
  obtain ⟨F,hF,hfin,_,⟨e⟩⟩ := model
  have hb : 3 ≤ primeRank 2 (ExceptionalSplit.E6 F) := by
    by_cases h2 : (2 : F) = 0
    · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
      exact Theory.SpecificGroups.LieType.TwoRank.e6_three_le F
    · exact Theory.SpecificGroups.LieType.TwoRank.odd_e6_three_le F h2
  rw [← primeRank_equiv 2 e] at hb
  omega

/-- Every literal E7 model is absent from the ordinary two-rank-two list. -/
theorem no_e7_model (hr : primeRank 2 Q ≤ 2) {q : ℕ}
    (model : ExceptionalGroup.IsE7 Q q) : False := by
  obtain ⟨F,hF,hfin,_,⟨e⟩⟩ := model
  have hb : 3 ≤ primeRank 2 (ExceptionalSplit.E7 F) := by
    by_cases h2 : (2 : F) = 0
    · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
      exact Theory.SpecificGroups.LieType.TwoRank.e7_three_le F
    · exact Theory.SpecificGroups.LieType.TwoRank.odd_e7_three_le F h2
  rw [← primeRank_equiv 2 e] at hb
  omega

/-- Every literal E8 model is absent from the ordinary two-rank-two list. -/
theorem no_e8_model (hr : primeRank 2 Q ≤ 2) {q : ℕ}
    (model : ExceptionalGroup.IsE8 Q q) : False := by
  obtain ⟨F,hF,hfin,_,⟨e⟩⟩ := model
  have hb : 3 ≤ primeRank 2 (ExceptionalSplit.E8 F) := by
    by_cases h2 : (2 : F) = 0
    · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
      exact Theory.SpecificGroups.LieType.TwoRank.e8_three_le F
    · exact Theory.SpecificGroups.LieType.TwoRank.odd_e8_three_le F h2
  rw [← primeRank_equiv 2 e] at hb
  omega

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p q : ℕ}

/-- The original source quotient cannot be E6, at any field parameter. -/
theorem CounterexampleToTheoremA.centralQuotient_no_e6_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsE6 (S ⧸ center S) q) : False :=
  Nonsemisimple.RankTwoSieve.no_e6_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model

/-- The original source quotient cannot be E7, at any field parameter. -/
theorem CounterexampleToTheoremA.centralQuotient_no_e7_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsE7 (S ⧸ center S) q) : False :=
  Nonsemisimple.RankTwoSieve.no_e7_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model

/-- The original source quotient cannot be E8, at any field parameter. -/
theorem CounterexampleToTheoremA.centralQuotient_no_e8_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsE8 (S ⧸ center S) q) : False :=
  Nonsemisimple.RankTwoSieve.no_e8_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model

end CFSG.Quasithin.ChapterA.Section02
