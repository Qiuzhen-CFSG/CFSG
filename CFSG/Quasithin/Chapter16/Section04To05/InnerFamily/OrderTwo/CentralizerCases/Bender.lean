module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.InnerExclusions
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Bender.MarkedActions
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Bender.MarkedUnitary

/-!
# Reduction of the Bender residual-centralizer cases

Suzuki quotients admit no outer involution, including exceptional central
covers. The remaining binary PSL₂ case has even field degree, with PSL₂(4)
retained; the unitary case has fixed-field degree at least two.
`MarkedActions` identifies the actual embedded linear residual and its
pointwise fixer after field-action normalization. `MarkedUnitary` provides
a standard Hermitian marking and transports a supplied graph conjugacy;
the graph-fixed embedded residual is proved to be the full fixed subgroup.

The intrinsic PSL₂ field-residual and PSU₃ graph-fixed pointwise-fixer
calculations remain necessary for `ResidualCentralizerAlternative`.
This module does not yet assert that alternative for the Bender family.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1170–1172, 1184 and the proof of 16.4.9(1) on p.1189.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Bender
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The two remaining model branches, with their exact source parameter ranges. -/
theorem bender_remaining_models (hG : HasEvenTypeCentralizers G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hmodel : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L)) :
    (∃ n : ℕ, 2 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 (2 ^ n)) := by
  cases hmodel with
  | linear n hn he => exact Or.inl ⟨n, hn, psl2_degree_even hG h hr hr2 hout he, he⟩
  | unitary n hn he => exact Or.inr ⟨n, hn, he⟩
  | suzuki m hm he => exact (no_suzuki hG h hr hr2 hout hm he.some).elim
end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Bender
