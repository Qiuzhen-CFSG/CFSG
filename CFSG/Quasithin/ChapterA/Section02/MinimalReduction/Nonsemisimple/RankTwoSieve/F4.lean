module
public import Theory.SpecificGroups.LieType.TwoRankLower.BinaryExceptional
public import Theory.SpecificGroups.LieType.TwoRankLower.OddF4
public import CFSG.KnownSimple.ExceptionalModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
/-!
# The full F4 branch of the original two-rank sieve

Binary Sp6 embeddings and odd-characteristic sign coroots exclude every
literal F4 model using the ordinary two-rank bound on the original quotient.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]
/-- Every literal F4 model is absent from the ordinary two-rank-two list. -/
theorem no_f4_model (hr : primeRank 2 Q ≤ 2) {q : ℕ}
    (model : ExceptionalGroup.IsF4 Q q) : False := by
  obtain ⟨F,hF,hfin,_,⟨e⟩⟩ := model
  let : Fact (ringChar F).Prime := ⟨CharP.prime_ringChar F⟩
  have hb : 3 ≤ primeRank 2 (ExceptionalSplit.F4 F) := by
    by_cases hp : ringChar F = 2
    · let : CharP F 2 := ringChar.of_eq hp
      exact Theory.SpecificGroups.LieType.TwoRank.f4_three_le F
    · exact Theory.SpecificGroups.LieType.TwoRank.F4Odd.three_le F (ringChar F) hp
  rw [← primeRank_equiv 2 e] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p q : ℕ}
/-- The original source quotient cannot be F4 at any field parameter. -/
theorem CounterexampleToTheoremA.centralQuotient_no_f4_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (model : ExceptionalGroup.IsF4 (S ⧸ center S) q) : False :=
  Nonsemisimple.RankTwoSieve.no_f4_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model
end CFSG.Quasithin.ChapterA.Section02
