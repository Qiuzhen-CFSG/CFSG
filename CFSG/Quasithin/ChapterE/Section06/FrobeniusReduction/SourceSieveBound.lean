module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCommonBound
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceComplete
/-!
# The original E.6.3 route with the complete E.6.8 source supplied

The adequate source theorem classifies each actual centralizer component
from E.6.1 alone. Applying it to the existing full-minimum argument removes
the entire E.6.8 premise. The earlier common-normal theorem, E.6.7, I.3,
regular-section construction and O’Nan factor existence are already supplied.
The two remaining source producers are the actual E.6.18 seven exclusion
and E.6.23 recognition of the further component.

Source: Aschbacher–Smith E.6.3 and E.6.8–25, printed pp.245–256.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components.RemainingSieve Hyperplanes Hyperplanes.Enlargement
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

theorem lower_bound_knownSimple_of_hyperplane_models [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (h18 : SevenExcluded M V)
    (hquot : SixAutomorphisms.ModelIdentification.QuotientRecognition T M V) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V :=
  lower_bound_knownSimple_of_remaining_models h hm h18
    (fun _ hA _ hX => adequateComponentAlternatives_knownSimple h hA hX) hquot
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
