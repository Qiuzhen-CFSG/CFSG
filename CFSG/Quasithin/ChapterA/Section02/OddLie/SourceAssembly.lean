module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Linear
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Unitary
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.SymplecticG2
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.CoverCases
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Exceptional
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Triality
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Orthogonal
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.G2Cover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.SymplecticCover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.LinearCover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryHigherCover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryTernary
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryCompletion
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.OrthogonalCover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.SplitSix
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.OrthogonalCompletion
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.HigherExceptional

/-!
# Checked odd-Lie source branches in the A.2 induction

The complete simple split-linear, unitary, symplectic, odd orthogonal,
nonsplit orthogonal and G₂ branches supply
the literal Theorem B and C models, with all parameter restrictions proved
from quasithinness. These models directly exclude the source Case I minimal
counterexample. PSL₂ and PSL₃ central quotients, including PSL₂(9), and all
large Ree, odd F₄, odd triality and all odd G₂ central quotients are excluded
in original Case II. The complete odd symplectic central-quotient branch
is excluded as well. Every odd split-linear central quotient and every
odd unitary central quotient are now excluded from original Case II,
including the exceptional PSU₄(3) partial-center quotients. The split-six comparison completes split orthogonal Case I. All three
odd orthogonal central-quotient families are now excluded in Case II:
the remaining ternary parameters have actual rank-four involution
centralizers, and all smaller aliases reduce to the completed linear,
symplectic and unitary branches.

The actual E₆, E₇, E₈ and twisted E₆ root charts now exclude all higher
exceptional branches, including the original source central covers with no
primary-center premise. The global catalogue dispatcher and source-only
center discharge for the earlier classical wrappers are assembled separately.
No statement here assumes quasithinness descends through arbitrary odd kernels.
Source: Aschbacher–Smith, A.2.13–17, printed pp.37–39.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem caseI_false_of_models [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    (hb : IsTheoremBModel G) (hc : IsStronglyQuasithin G → IsTheoremCModel G) : False := by
  rcases (h.simple_case inferInstance).2.2.2 with hB | ⟨hs, hC⟩
  · exact hB hb
  · exact hC (hc hs)

/-- Literal Case I application for every split-linear catalogue parameter. -/
theorem linear_minimal_counterexample_false [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    {r e n : ℕ} [Fact r.Prime] (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSL G n (r^e)) : False := by
  obtain ⟨hb,hc⟩ := linear_caseI hn hr he (h.simple_case inferInstance).2.1 model
  exact caseI_false_of_models h hb hc

/-- Literal Case I application for every unitary catalogue parameter. -/
theorem unitary_minimal_counterexample_false [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    {r e n : ℕ} [Fact r.Prime] (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSU G n (r^e)) : False := by
  obtain ⟨hb,hc⟩ := unitary_caseI hn hr he (h.simple_case inferInstance).2.1 model
  exact caseI_false_of_models h hb hc

/-- Literal Case I application for every symplectic catalogue parameter. -/
theorem symplectic_minimal_counterexample_false [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    {r e n : ℕ} [Fact r.Prime] (hn : 1 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSp G n (r^e)) : False := by
  obtain ⟨hb,hc⟩ := symplectic_caseI hn hr he (h.simple_case inferInstance).2.1 model
  exact caseI_false_of_models h hb hc

/-- Literal Case I application for every odd G₂ catalogue parameter. -/
theorem g2_minimal_counterexample_false [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    {r e : ℕ} [Fact r.Prime] (hr : Odd r) (he : 1 ≤ e)
    (model : ClassificationModels.IsG2At G (r^e)) : False := by
  obtain ⟨hb,hc⟩ := g2_caseI hr he (h.simple_case inferInstance).2.1 model
  exact caseI_false_of_models h hb hc
/-- Literal Case I application for every odd orthogonal catalogue parameter. -/
theorem orthogonal_odd_minimal_counterexample_false [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    {r e n : ℕ} [Fact r.Prime] (hn : 1 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaOdd G n (r^e)) : False := by
  obtain ⟨hb,hc⟩ := orthogonal_odd_caseI hn hr he (h.simple_case inferInstance).2.1 model
  exact caseI_false_of_models h hb hc

/-- Literal Case I application for every nonsplit orthogonal catalogue parameter. -/
theorem orthogonal_minus_minimal_counterexample_false [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    {r e n : ℕ} [Fact r.Prime] (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaMinus G n (r^e)) : False := by
  obtain ⟨hb,hc⟩ := orthogonal_minus_caseI hn hr he (h.simple_case inferInstance).2.1 model
  exact caseI_false_of_models h hb hc
/-- Literal Case I application for the full split orthogonal catalogue,
including the retained six-dimensional linear alias. -/
theorem orthogonal_plus_full_minimal_counterexample_false [IsSimpleGroup G]
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G)
    {r e n : ℕ} [Fact r.Prime] (hn : 3 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaPlus G n (r^e)) : False := by
  obtain ⟨hb,hc⟩ := orthogonal_plus_caseI hn hr he (h.simple_case inferInstance).2.1 model
  exact caseI_false_of_models h hb hc

end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
