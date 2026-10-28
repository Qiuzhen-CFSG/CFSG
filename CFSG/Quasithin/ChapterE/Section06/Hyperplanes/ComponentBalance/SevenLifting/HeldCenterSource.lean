module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.ConcreteSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.RudvalisSource

/-!
# The original E.6.18 reduction after the Rudvalis calculation

The literal second Rudvalis centralizer has order 116480, prime to three.
This discharges the last numerical entry of the complete model inspection.
The original ambient exclusion therefore retains only the Held perfect-cover
center theorem; its actual actions, quotient maps and earlier source inputs
are those of the existing source assembly. No unrestricted Held inspection
is asserted.

Source: Aschbacher--Smith E.6.18, printed p.252.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
universe u

/-- All catalogue entries used by the source dispatch have concrete producers. -/
theorem sevenInspectionModelFacts_source : SevenInspectionModelFacts :=
  sevenInspectionModelFacts_of_rudvalis_order
    Rudvalis.InvolutionCentralizers.second_centralizer_not_nine

/-- The remaining Held cover-center premise is isolated on the original
E.6.18 consumer, without any global automorphism-inspection assumption. -/
theorem sevenExcluded_of_held_center
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {M V : Subgroup G}
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (h15 : HypothesisE615 V) :
    Enlargement.SevenExcluded M V :=
  sevenExcluded_of_remaining_model_facts sevenInspectionModelFacts_source hHeld h h15

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
