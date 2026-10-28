module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.SplitSix
public import Theory.SpecificGroups.ClassicalOrthogonal.OddSevenTernaryCover.Higher

/-!
# Complete odd orthogonal Case II of A.2.17

The actual fundamental root subgroups reduce every higher central quotient
to the ternary field. In that field an embedded minus-six block supplies a
nontrivial involution and an elementary subgroup of order 81 in its
centralizer, for all three orthogonal signs. The odd-central-extension rank
bound contradicts quasithinness of the original covering group. The small
linear, symplectic and unitary aliases retain their exact field parameters.

Source: Aschbacher–Smith A.2.17, printed pp.38–39; I.2.1, printed p.409.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G]
  [Group S] [Finite S] [IsQuasisimple G] {p : ℕ}

omit [IsQuasisimple G] in
private theorem center_odd
    (h : CounterexampleToTheoremA K G S p) (hP : IsPGroup p (center G)) :
    Odd (Nat.card (center G)) := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  obtain ⟨k,hk⟩ := hP.exists_card_eq
  rw [hk]
  exact h.2.2.2.2.2.1.pow

/-- Every odd-dimensional orthogonal central quotient is excluded in original Case II. -/
public theorem orthogonal_odd_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {n r e : ℕ} [Fact r.Prime]
    (hn : 1 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaOdd (G ⧸ center G) n (r^e)) : False := by
  obtain ⟨hn3,rfl,rfl⟩ := orthogonal_odd_caseII_parameters h ih hP hn hr he model
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  exact ClassicalOrthogonal.OddSevenTernaryCover.not_isQuasithin_of_odd_quotient_equiv
    hn3 (by simpa using hcard) iso (center_odd h hP) h.1

/-- Every split orthogonal central quotient, including rank three, is excluded. -/
public theorem orthogonal_plus_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {n r e : ℕ} [Fact r.Prime]
    (hn : 3 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaPlus (G ⧸ center G) n (r^e)) : False := by
  by_cases h3 : n = 3
  · subst n
    exact orthogonal_plus_three_caseII h ih hP hr he model
  have hn4 : 4 ≤ n := by omega
  obtain ⟨rfl,rfl⟩ := orthogonal_plus_caseII_parameters h hP hn4 hr he model
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  exact ClassicalOrthogonal.OddSevenTernaryCover.not_isQuasithin_of_plus_quotient_equiv
    hn4 (by simpa using hcard) iso (center_odd h hP) h.1

/-- Every nonsplit orthogonal central quotient is excluded, including minus-six. -/
public theorem orthogonal_minus_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {n r e : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) n (r^e)) : False := by
  by_cases h3 : n = 3
  · subst n
    exact orthogonal_minus_three_caseII h ih hP hr he model
  obtain ⟨hn3,rfl,rfl⟩ := orthogonal_minus_caseII_parameters h ih hP hn hr he model
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  exact ClassicalOrthogonal.OddSevenTernaryCover.not_isQuasithin_of_minus_quotient_equiv
    (by omega) (by simpa using hcard) iso (center_odd h hP) h.1
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
