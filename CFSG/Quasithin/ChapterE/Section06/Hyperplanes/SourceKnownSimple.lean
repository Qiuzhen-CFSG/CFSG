module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceRecognition
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.SourceKnownSimple

/-!
# Known-simple E.6.23 rank assembly

The E.6.8 component sieve is already a complete theorem for
`KnownSimple.IsKnownSimple`.  This upper-layer adapter feeds it to the
E.6.23 rank consumer, leaving only the original E.6.18 exclusion and common
normal input.  The lower component-balance wrappers live in the
`ComponentBalance.OddObstruction` extension.

Source: Aschbacher--Smith, E.6.8 and E.6.23, printed pp.247--255.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes
open Components ComponentBalance Enlargement
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

/-- E.6.23's rank conclusion with the known-simple E.6.8 sieve discharged. -/
theorem source_rank_gt_one_knownSimple [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h18 : SevenExcluded M V) :
    1 < globalR V :=
  Enlargement.source_rank_gt_one h hm h311 h18
    (adequate_models_knownSimple h)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
