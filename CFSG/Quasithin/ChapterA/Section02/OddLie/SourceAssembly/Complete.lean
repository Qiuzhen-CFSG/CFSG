module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.Models
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.OriginalSource
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.HigherExceptional
/-!
# Complete odd-Lie source dispatch for A.2.17

All fourteen odd-characteristic carrier constructors are handled with their
literal field and model data. In the simple case they supply the full
Theorem B and C lists. In the original quasisimple counterexample case,
the actual scalar, root and exceptional-cover arguments give a contradiction
without a primary-center or quotient-quasithinness assumption.
The final simple-case application excludes the actual minimal counterexample.
Source: Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.OddLie
open SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]

theorem caseI_of_oddLieCarrier [IsSimpleGroup G]
    (hqt : IsQuasithin G) (model : IsOddLieCarrier G) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  cases model with
  | linear d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact linear_caseI hp.2.1 ho he hqt model
  | unitary d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact unitary_caseI hp.2.1 ho he hqt model
  | symplectic d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact symplectic_caseI hp.2.1 ho he hqt model
  | orthogonalPlus d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact orthogonal_plus_caseI hp.2 ho he hqt model
  | orthogonalOdd d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact orthogonal_odd_caseI hp.2.1 ho he hqt model
  | orthogonalMinus d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact orthogonal_minus_caseI hp.2 ho he hqt model
  | g2 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact g2_caseI ho he hqt model
  | ree q model => exact (ree_caseI_false hqt model).elim
  | triality P ho model =>
    obtain ⟨iso⟩ := model
    exact (triality_caseI_false P ho hqt iso).elim
  | f4 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact (f4_caseI_false ho hqt model).elim
  | e6 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact (e6_caseI_false ho hqt model).elim
  | e7 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact (e7_caseI_false ho hqt model).elim
  | e8 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact (e8_caseI_false ho hqt model).elim
  | twistedE6 r e hr ho he model =>
    exact (twisted_e6_caseI_false ho.pow hqt model).elim

variable {K : GroupClass.{u}} {S : Type u} [Group S] [Finite S] {p : ℕ}

theorem caseII_of_oddLieCarrier [IsQuasisimple G]
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (model : IsOddLieCarrier (G ⧸ center G)) : False := by
  cases model with
  | linear d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact linear_caseII_of_source h ih hp.2.1 ho he model
  | unitary d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact unitary_caseII_of_source h ih hp.2.1 ho he model
  | symplectic d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact symplectic_caseII_of_source h ih hp.2.1 ho he model
  | orthogonalPlus d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact orthogonal_plus_caseII_of_source h ih hp.2 ho he model
  | orthogonalOdd d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact orthogonal_odd_caseII_of_source h ih hp.2.1 ho he model
  | orthogonalMinus d r e hr ho he hp model =>
    let : Fact r.Prime := ⟨hr⟩
    exact orthogonal_minus_caseII_of_source h ih hp.2 ho he model
  | g2 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact g2_caseII_of_source h ih ho he model
  | ree q model => exact ree_caseII_false_of_source h ih model
  | triality P ho model =>
    obtain ⟨iso⟩ := model
    exact triality_caseII_false_of_source h ih P ho iso
  | f4 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact f4_caseII_false_of_source h ih ho model
  | e6 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact e6_caseII_false h ih ho model
  | e7 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact e7_caseII_false h ih ho model
  | e8 r e hr ho he model =>
    let : Fact r.Prime := ⟨hr⟩
    exact e8_caseII_false h ih ho model
  | twistedE6 r e hr ho he model =>
    exact twisted_e6_caseII_false h ih ho.pow model

theorem not_minimalCounterexample_oddLieCarrier [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    (model : IsOddLieCarrier G) : False := by
  obtain ⟨hna,hqt,hK,hB | ⟨hs,hC⟩⟩ := h.simple_case inferInstance
  · exact hB (caseI_of_oddLieCarrier hqt model).1
  · exact hC ((caseI_of_oddLieCarrier hqt model).2 hs)

end CFSG.Quasithin.ChapterA.Section02.OddLie
