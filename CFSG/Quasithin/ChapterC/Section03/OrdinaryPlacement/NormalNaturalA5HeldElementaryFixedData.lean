module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryClasses
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate.Data
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Action

/-!
# Native fixed-vertex counts for the two elementary Held rows

Outside the six common fixed vertices, at most ten of the exact listed
row elements outside class 2A fix a given vertex. Both the identity and
all 2B elements are counted. The actual permutation evaluator, the exact
class label and every one of the 2058 vertices enter the kernel check.
-/

namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldElementaryCentralizer.FixedData
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- The complete finite vertex bound, in the unchanged catalogue coordinates. -/
public theorem pure_members_fixing_card_le (k : Fin 2) : ∀ x : Fin 2058,
    x ∉ sextet k →
      (((members (some (row k))).filter (fun n =>
        !Held.OrdinaryElementary.classA n && decide (normalFormAction n x = x))).toFinset).card
          ≤ 10 := by
  fin_cases k <;> apply Held.TwoLocalCandidates.Cores.allLetters <;> decide +kernel

end CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldElementaryCentralizer.FixedData
