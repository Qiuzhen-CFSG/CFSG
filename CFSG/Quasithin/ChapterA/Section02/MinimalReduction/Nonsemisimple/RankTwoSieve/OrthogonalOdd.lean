module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.OddParameters
public import Theory.SpecificGroups.ClassicalOrthogonal.TwoRankLower.Odd
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison

/-!
# Odd-dimensional orthogonal entries and the minus-four alias

The actual PSp₄ subgroups exclude all odd orthogonal ranks at least two.
Rank one is the actual PSL₂ model over the same field. The minus-four
comparison uses its actual quadratic extension field, including characteristic
two, so these low-rank entries are retained in the source's PSL₂ alternative.
Source: GLS3 §2.7; Aschbacher–Smith A.2.12, printed p.36.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- Higher odd-dimensional orthogonal models contain an actual elementary eight. -/
theorem orthogonal_odd_rank_le_one (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hm : ClassicalGroup.IsPOmegaOdd Q r q) : r ≤ 1 := by
  by_contra hn
  obtain ⟨F,hF,hfin,_,⟨a⟩⟩ := hm
  have hb := ClassicalOrthogonal.TwoRank.odd_three_le F (by omega : 2 ≤ r)
  rw [← primeRank_equiv 2 a] at hb
  omega

/-- The full admissible odd-dimensional family reduces to the literal PSL₂ alias. -/
theorem orthogonal_odd_linear_two (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hpos : 1 ≤ r) (hm : ClassicalGroup.IsPOmegaOdd Q r q) :
    r=1 ∧ ClassicalGroup.IsPSL Q 2 q := by
  have he : r=1 := by have := orthogonal_odd_rank_le_one hr hm; omega
  subst r
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
  exact ⟨rfl,F,hF,hfin,hcard,⟨a.trans ClassicalOrthogonal.RankOneComparison.projectiveEquivPSL⟩⟩

omit [Finite Q] in
/-- The genuine minus-four carrier is PSL₂ over its quadratic field, in every characteristic. -/
theorem orthogonal_minus_two_linear {q : ℕ}
    (hm : ClassicalGroup.IsPOmegaMinus Q 2 q) : ClassicalGroup.IsPSL Q 2 (q^2) := by
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
  obtain ⟨E,hE,hEfin,hEcard,⟨b⟩⟩ := ClassicalOrthogonal.Minus.OddFourComparison.exists_projectiveEquivPSL F
  exact ⟨E,hE,hEfin,by simpa only [hcard] using hEcard,⟨a.trans b⟩⟩

variable [Group.IsPerfect Q]
/-- All simple-range odd-dimensional models lie in the exact odd PSL₂ source alternative. -/
theorem orthogonal_odd_source_models (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hp : KnownSimple.OrthogonalOddParameters r q) (hm : ClassicalGroup.IsPOmegaOdd Q r q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 3 q := by
  obtain ⟨he,hl⟩ := orthogonal_odd_linear_two hr hp.2.1 hm
  exact linear_source_models hr (by decide) (fun _ => hp.2.2.1 he) hl

/-- The minus-four alias lies in the same completed linear branch. -/
theorem orthogonal_minus_two_source_models (hr : primeRank 2 Q ≤ 2) {q : ℕ}
    (hm : ClassicalGroup.IsPOmegaMinus Q 2 q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 3 q := by
  have hl := orthogonal_minus_two_linear hm
  have hq2 : 2 ≤ q := by
    obtain ⟨F,hF,hfin,hcard,_⟩ := hm
    rw [← hcard]
    exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  exact linear_source_models hr (by decide) (fun _ => by nlinarith) hl
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- Full odd-dimensional orthogonal family inspection on the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_orthogonal_odd_source_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {r q : ℕ}
    (hp : KnownSimple.OrthogonalOddParameters r q)
    (hm : ClassicalGroup.IsPOmegaOdd (S ⧸ center S) r q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q := by
  let := h.2.2.2.1.isPerfect
  exact Nonsemisimple.RankTwoSieve.orthogonal_odd_source_models
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hp hm
/-- Literal source application of the minus-four quadratic-field alias. -/
theorem CounterexampleToTheoremA.centralQuotient_orthogonal_minus_two_source_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {q : ℕ}
    (hm : ClassicalGroup.IsPOmegaMinus (S ⧸ center S) 2 q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q := by
  let := h.2.2.2.1.isPerfect
  exact Nonsemisimple.RankTwoSieve.orthogonal_minus_two_source_models
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hm
end CFSG.Quasithin.ChapterA.Section02
