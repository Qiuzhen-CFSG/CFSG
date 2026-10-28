module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.OrthogonalOdd
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.SimpleQuotient
public import Theory.SpecificGroups.ClassicalOrthogonal.TwoRankLower.MinusOdd
public import Theory.SpecificGroups.ClassicalOrthogonal.TwoRankLower.MinusBinary
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.Binary

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.UnitaryHigher

/-!
# The complete minus-orthogonal source branch

Actual elementary eights exclude every rank at least four. In rank three,
odd fields are excluded by the centerless five-space; characteristic two
uses the literal exterior-square comparison with PSU₄ and its proved rank
bound. Rank two is retained as PSL₂(q²), including the binary field.
Source: GLS3 §2.7; Aschbacher–Smith A.2.12, printed p.36.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

theorem orthogonal_minus_rank_le_three (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hm : ClassicalGroup.IsPOmegaMinus Q r q) : r ≤ 3 := by
  by_contra hd
  obtain ⟨F,hF,hfin,_,⟨a⟩⟩ := hm
  have hb : 3 ≤ primeRank 2 (ClassicalGroup.POmegaMinus r F) := by
    by_cases h2 : (2:F)=0
    · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
      exact ClassicalOrthogonal.TwoRank.minus_binary_four_le (by omega)
    · exact ClassicalOrthogonal.TwoRank.minus_odd_three_le h2 (by omega)
  rw [← primeRank_equiv 2 a] at hb
  omega

variable [IsSimpleGroup Q]
theorem orthogonal_minus_three_unitary_four (hr : primeRank 2 Q ≤ 2) {q : ℕ}
    (hm : ClassicalGroup.IsPOmegaMinus Q 3 q) : ClassicalGroup.IsPSU Q 4 q := by
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
  have h2 : (2:F)=0 := by
    by_contra h2
    have hb := ClassicalOrthogonal.TwoRank.minus_odd_three_le h2 (by decide : 3 ≤ 3)
    rw [← primeRank_equiv 2 a] at hb
    omega
  let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
  let : Fintype F := Fintype.ofFinite F
  let : IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F) := a.isSimpleGroup_congr.mp inferInstance
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hcn : Nat.card F = 2^(n:ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  obtain ⟨E,hE,hEfin,J,hEc,hconj,⟨b⟩⟩ :=
    ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.exists_comparison_pos
      (n:ℕ) n.pos hcn
  have hq : q=2^(n:ℕ) := hcard.symm.trans hcn
  rw [← hq] at hEc hconj
  exact ⟨E,hE,hEfin,J,hEc,hconj,⟨a.trans b⟩⟩

/-- All actual minus carriers in the catalogue reduce to their genuine rank-two alias. -/
theorem orthogonal_minus_rank_eq_two (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters r q)
    (hm : ClassicalGroup.IsPOmegaMinus Q r q) : r=2 := by
  have hd := orthogonal_minus_rank_le_three hr hm
  have he : r=2 ∨ r=3 := by have := hp.2; omega
  rcases he with he | rfl
  · exact he
  · exact (no_unitary_higher_model hr (by decide) hp.1
      (orthogonal_minus_three_unitary_four hr hm)).elim

variable [Group.IsPerfect Q]
/-- The full minus family lies in the completed odd-linear alternatives. -/
theorem orthogonal_minus_source_models (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters r q)
    (hm : ClassicalGroup.IsPOmegaMinus Q r q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 3 q := by
  obtain rfl := orthogonal_minus_rank_eq_two hr hp hm
  exact orthogonal_minus_two_source_models hr hm
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- The complete minus family on the original source quotient, with no rank or simplicity premise. -/
theorem CounterexampleToTheoremA.centralQuotient_orthogonal_minus_source_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {r q : ℕ} (hp : KnownSimple.OrthogonalMinusParameters r q)
    (hm : ClassicalGroup.IsPOmegaMinus (S ⧸ center S) r q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q := by
  let := h.2.2.2.1.isPerfect
  let := h.section_centralQuotient_simple_of_not_semisimple ih hn
  exact Nonsemisimple.RankTwoSieve.orthogonal_minus_source_models
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hp hm
end CFSG.Quasithin.ChapterA.Section02
