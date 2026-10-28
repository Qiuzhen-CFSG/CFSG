module

public import CFSG.KnownSimple.ClassicalModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SU3.EvenTwoRank

/-!
# Binary endpoints of the degree-two and degree-three families

The root subgroup bounds the binary PSL₂ degree by two. The exact ranks
2n for PSL₃(2ⁿ) and n for PSU₃(2ⁿ) bound their degrees by one and two.
The simple-range unitary catalogue excludes n=1, leaving precisely PSU₃(4).
All statements use the stored actual matrix-model equivalences.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- A binary linear degree-two model with two-rank at most two has exponent at most two. -/
theorem psl_two_binary_exponent_le_two (hr : primeRank 2 Q ≤ 2) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) : n ≤ 2 := by
  obtain ⟨F, hF, hfin, hcard, ⟨a⟩⟩ := hmodel
  rw [Theory.GroupTheory.primeRank_equiv 2 a] at hr
  exact (Theory.PSL2.root_two_rank_ge F hcard).trans hr

/-- The binary linear degree-three family reduces to its field of order two. -/
theorem psl_three_binary_exponent_eq_one (hr : primeRank 2 Q ≤ 2) {n : ℕ}
    (hn : 0 < n) (hmodel : ClassicalGroup.IsPSL Q 3 (2 ^ n)) : n = 1 := by
  obtain ⟨F, hF, hfin, hcard, ⟨a⟩⟩ := hmodel
  rw [Theory.GroupTheory.primeRank_equiv 2 a, Matrix.PSL3Even.two_rank F hn hcard] at hr
  omega

/-- The binary unitary degree-three family has fixed-field exponent at most two. -/
theorem psu_three_binary_exponent_le_two (hr : primeRank 2 Q ≤ 2) {n : ℕ}
    (hn : 0 < n) (hmodel : ClassicalGroup.IsPSU Q 3 (2 ^ n)) : n ≤ 2 := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨a⟩⟩ := hmodel
  rw [Theory.GroupTheory.primeRank_equiv 2 a,
    BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J hn hcard hconj] at hr
  exact hr

/-- With the genuine simple-range parameter restriction, the endpoint is PSU₃(4). -/
theorem psu_three_four_of_binary_model (hr : primeRank 2 Q ≤ 2) {n : ℕ}
    (hn : 0 < n) (hne : 2 ^ n ≠ 2)
    (hmodel : ClassicalGroup.IsPSU Q 3 (2 ^ n)) : ClassicalGroup.IsPSU Q 3 4 := by
  have hle := psu_three_binary_exponent_le_two hr hn hmodel
  have he : n = 2 := by
    have hn1 : n ≠ 1 := by intro h; simp [h] at hne
    omega
  simpa only [he, show (2 : ℕ) ^ 2 = 4 from rfl] using hmodel

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- Binary PSL₂ field bound on the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_psl_two_binary_exponent_le_two
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL (S ⧸ center S) 2 (2 ^ n)) : n ≤ 2 :=
  Nonsemisimple.RankTwoSieve.psl_two_binary_exponent_le_two
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hmodel

/-- Binary PSL₃ field reduction on the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_psl_three_binary_exponent_eq_one
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {n : ℕ} (hn0 : 0 < n)
    (hmodel : ClassicalGroup.IsPSL (S ⧸ center S) 3 (2 ^ n)) : n = 1 :=
  Nonsemisimple.RankTwoSieve.psl_three_binary_exponent_eq_one
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hn0 hmodel

/-- The sole admissible binary PSU₃ endpoint for the original source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_psu_three_four_of_binary_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {n : ℕ} (hn0 : 0 < n) (hne : 2 ^ n ≠ 2)
    (hmodel : ClassicalGroup.IsPSU (S ⧸ center S) 3 (2 ^ n)) :
    ClassicalGroup.IsPSU (S ⧸ center S) 3 4 :=
  Nonsemisimple.RankTwoSieve.psu_three_four_of_binary_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hn0 hne hmodel

end CFSG.Quasithin.ChapterA.Section02
