module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models

/-!
# The component Borel calculation required in E.6.25

The output permits replacement of the cyclic subgroup while preserving its
actual action image on V. Every odd actor whose induced action commutes with
that image must commute with the replacement modulo the intrinsic two-core
of L ∩ M. This is an output specification, with separate proofs for the
component models; it is not an additional hypothesis of E.6.11.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3b)
and the factor-count paragraph of E.6.25, printed pp.249–250,255.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
variable {G : Type*} [Group G]

/-- The local output used by the conjugate-candidate assembly. -/
def ComponentBorelLiftConclusion (M V U L X : Subgroup G) : Prop :=
  ∃ Y : Subgroup G, Y ≤ L ∧ RegularCyclicSection M V U Y ∧
    inducedAutomizer V Y = inducedAutomizer V X ∧
    ∀ A : Subgroup G, A ≤ normalizer (V : Set G) → Odd (Nat.card A) →
      (∀ a ∈ inducedAutomizer V A, ∀ y ∈ inducedAutomizer V Y, Commute a y) →
      ⁅A, Y⁆ ≤ (L ⊓ M).pCoreIn 2

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
