module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.LinearModels
public import Theory.SpecificGroups.Symplectic.TwoRankLower
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne

/-!
# The complete symplectic branch of the two-rank-two sieve

Actual elementary eights exclude every symplectic entry of half-dimension
at least two. The remaining rank-one matrix carrier is identified with PSL₂
through the existing form-preserving reindexing. The linear-family reduction
then puts it into the source's odd-field alternatives, including the small
binary exceptional isomorphism.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- Every higher symplectic catalogue entry is excluded by its elementary eight. -/
theorem symplectic_rank_le_one (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hmodel : ClassicalGroup.IsPSp Q r q) : r ≤ 1 := by
  by_contra hn
  obtain ⟨F,hF,hfin,_,⟨a⟩⟩ := hmodel
  have hb := Theory.SpecificGroups.Symplectic.TwoRank.three_le F (by omega : 2 ≤ r)
  rw [← primeRank_equiv 2 a] at hb
  omega

/-- In the actual simple parameter range only the rank-one PSL₂ alias remains. -/
theorem symplectic_linear_two (hr : primeRank 2 Q ≤ 2) {r q : ℕ} (hr0 : 1 ≤ r)
    (hmodel : ClassicalGroup.IsPSp Q r q) : r = 1 ∧ ClassicalGroup.IsPSL Q 2 q := by
  have he : r = 1 := by have := symplectic_rank_le_one hr hmodel; omega
  subst r
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hmodel
  exact ⟨rfl,F,hF,hfin,hcard,⟨a.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩

/-- The full admissible symplectic catalogue branch lies in the odd-field source alternatives. -/
theorem symplectic_models_of_twoRank_le_two (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hr0 : 1 ≤ r) (hq : r = 1 → 4 ≤ q) (hmodel : ClassicalGroup.IsPSp Q r q) :
    (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL Q 3 q := by
  obtain ⟨he,hm⟩ := symplectic_linear_two hr hr0 hmodel
  exact linear_models_of_twoRank_le_two hr (by decide) (fun _ => hq he) hm

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The complete symplectic family inspection on the literal source quotient S/Z(S). -/
theorem CounterexampleToTheoremA.centralQuotient_symplectic_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hns : ¬ IsSemisimple G) {r q : ℕ} (hr : 1 ≤ r) (hq : r = 1 → 4 ≤ q)
    (hmodel : ClassicalGroup.IsPSp (S ⧸ center S) r q) :
    (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      ∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q :=
  Nonsemisimple.RankTwoSieve.symplectic_models_of_twoRank_le_two
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hns) hr hq hmodel

end CFSG.Quasithin.ChapterA.Section02
