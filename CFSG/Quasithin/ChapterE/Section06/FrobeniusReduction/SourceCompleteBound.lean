module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceRecognitionBound
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.HeldCenter

/-!
# The E.6.3 rank bounds with all model premises discharged

The proved Held odd-center theorem completes E.6.18. Supplying its exclusion
to the existing recognition and full-minimum argument gives the E.6.3 bounds
on the original group and elementary module under E.6.1 and m > 2.

Source: Aschbacher--Smith E.6.3 and E.6.18--25, printed pp.245,252--256.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
universe u

/-- E.6.3 for the full known-simple catalogue, with the Held cover-center
and all other model premises supplied by their proved producers. -/
theorem lower_bound_knownSimple
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V :=
  lower_bound_knownSimple_of_sevenExcluded h hm
    (Hyperplanes.ComponentBalance.sevenExcluded_knownSimple h (Or.inr hm))

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
