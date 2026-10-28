module
public import Theory.SpecificGroups.ClassicalOrthogonal.D3ExteriorComparison.General
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.OrthogonalCover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryCompletion
public import Theory.SpecificGroups.ClassicalOrthogonal.OddSevenTernaryCover

/-!
# The small odd orthogonal source aliases and ternary odd-seven obstruction

The exterior-square comparison covers the rank-three split entry retained
in the full classical catalogue. It transfers both original A.2.17 cases
to the complete linear family. The already marked minus-six comparison
now uses the complete unitary cover theorem, and the actual ternary
odd-seven centralizer excludes its odd central extensions.
Source: Aschbacher–Smith A.2.17, printed pp.38–39.
-/

open Subgroup Theory.GroupTheory
namespace ClassicalGroup
public theorem IsPOmegaPlus.three_isPSL_four
    {G : Type*} [Group G] {q : ℕ} (hq : Odd q)
    (model : IsPOmegaPlus G 3 q) : IsPSL G 4 q := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F (by rwa [hcard])
  exact ⟨F,hF,hfin,hcard,⟨iso.trans
    (ClassicalOrthogonal.D3ExteriorComparison.General.projectiveEquiv h2).symm⟩⟩
end ClassicalGroup

namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- Full split orthogonal Case I, including the actual six-dimensional alias. -/
public theorem orthogonal_plus_caseI {n r e : ℕ} [Fact r.Prime]
    (hn : 3 ≤ n) (hr : Odd r) (he : 1 ≤ e) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPOmegaPlus G n (r^e)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  by_cases h3 : n = 3
  · subst n
    exact linear_caseI (by decide) hr he hqt (model.three_isPSL_four hr.pow)
  exact (orthogonal_plus_caseI_false (by omega) hr hqt model).elim

universe u
variable {K : GroupClass.{u}} {G₀ S : Type u} [Group G₀] [Finite G₀]
  [Group S] [Finite S] [IsQuasisimple G₀] {p : ℕ}

/-- The genuine rank-three split central quotient reduces to PSL₄ over the same field. -/
public theorem orthogonal_plus_three_caseII
    (h : CounterexampleToTheoremA K G₀ S p) (ih : TheoremsOnProperSections K G₀)
    (hP : IsPGroup p (center G₀)) {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaPlus (G₀ ⧸ center G₀) 3 (r^e)) : False :=
  linear_caseII h ih hP (by decide) hr he (model.three_isPSL_four hr.pow)

/-- The actual minus-six cover is excluded by the completed unitary source family. -/
public theorem orthogonal_minus_three_caseII
    (h : CounterexampleToTheoremA K G₀ S p) (ih : TheoremsOnProperSections K G₀)
    (hP : IsPGroup p (center G₀)) {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaMinus (G₀ ⧸ center G₀) 3 (r^e)) : False := by
  let : IsSimpleGroup (G₀ ⧸ center G₀) := IsQuasisimple.simple
  exact unitary_caseII h ih hP (by decide) hr he
    (SmallIsomorphisms.isPSU_four_of_isPOmegaMinus_three hr.pow model)

omit [IsQuasisimple G₀] in
/-- Ω₇(3), with its literal marked central quotient, cannot occur in source Case II. -/
public theorem orthogonal_odd_three_caseII
    (h : CounterexampleToTheoremA K G₀ S p)
    (hP : IsPGroup p (center G₀))
    (model : ClassicalGroup.IsPOmegaOdd (G₀ ⧸ center G₀) 3 3) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  have ho : Odd (Nat.card (center G₀)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  exact ClassicalOrthogonal.OddSevenTernaryCover.not_isQuasithin_of_quotient_equiv hcard iso ho h.1
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
