module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.OrthogonalPlus
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.OrthogonalMinus
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.UnitaryModels

/-!
# All six classical families in the A.2.12 survivor list

The literal linear, unitary, symplectic and orthogonal model reducers cover
every constructor and every catalogue parameter. Low-rank aliases are
transported through genuine matrix equivalences. Higher ranks contain actual
elementary eights; the binary low-degree endpoints are reduced explicitly.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]

theorem classical_source_models (hr : primeRank 2 Q ≤ 2)
    (hm : KnownSimple.IsClassicalModel Q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
    (∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 3 q) ∨
    (∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSU Q 3 q) ∨
      ClassicalGroup.IsPSU Q 3 4 := by
  cases hm with
  | linear n q hp hm =>
    rcases linear_source_models hr hp.2.1 hp.2.2 hm with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  | unitary n q hp hm =>
    rcases unitary_source_models hr hp hm with (ha | hb) | hc | hd
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hd))
  | symplectic r q hp hm =>
    rcases symplectic_source_models hr hp.2.1 hp.2.2.1 hm with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  | orthogonalPlus r q hp hm => exact (no_orthogonal_plus_model hr hp.2 hm).elim
  | orthogonalOdd r q hp hm =>
    rcases orthogonal_odd_source_models hr hp hm with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  | orthogonalMinus r q hp hm =>
    rcases orthogonal_minus_source_models hr hp hm with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- Every classical catalogue entry for the actual source quotient is an established survivor. -/
theorem CounterexampleToTheoremA.centralQuotient_classical_source_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (hm : KnownSimple.IsClassicalModel (S ⧸ center S)) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
    (∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q) ∨
    (∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSU (S ⧸ center S) 3 q) ∨
      ClassicalGroup.IsPSU (S ⧸ center S) 3 4 := by
  let := h.2.2.2.1.isPerfect
  let := h.section_centralQuotient_simple_of_not_semisimple ih hn
  exact Nonsemisimple.RankTwoSieve.classical_source_models
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hm
end CFSG.Quasithin.ChapterA.Section02
