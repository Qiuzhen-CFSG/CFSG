module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Remaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.Source

/-!
# The original non-A₅ quasisimple point inspection

Every containing central quotient has now been compared with the actual
local image and moved subgroup. Both source inspection contracts and the
quasisimple exclusion are unconditional under their original hypotheses.
No irreducibility of an arbitrary FundamentalSetup is used; fixed layers,
nonsplit sections and the four-natural binary-three row are retained.

The original point-control application below discharges its quasisimple
premise. Full point control still requires fixed support/module choice
from `qt-d-10-nona5-point-selection`, the stabilizer normalizer and half-Sylow
uniqueness from `qt-d-10-nona5-half-sylow-unique`, and constrained exclusion
from `qt-d-10-nona5-point-constrained`. Their final unconditional discharge
remains with `qt-d-10-nona5-point-control`. The direct rank-one consumer
avoids the stronger uniform fixed-layer assertion.
Source: Aschbacher--Smith 10.2.9, printed pp.750--753.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The complete rank-two source inspection on the literal escaping component. -/
theorem rankTwoInspectionAt : RankTwoInspectionAt T := by
  intro _hmany L D _hminimal _hna t v I c hI hm
  let := hI
  exact (RankTwo.not_rank_two D c hm).elim

/-- Every complementary carrier is excluded under the original non-A₅ hypotheses. -/
theorem otherInspectionAt : OtherInspectionAt T := by
  intro _hmany L D _hminimal hna t v I c hI _hmodel _hrank
  let := hI
  exact (quasisimple_impossible D c hna).elim

/-- Both original inspections discharge the quasisimple source premise. -/
theorem quasisimpleExclusionAt : QuasisimpleExclusionAt T :=
  quasisimpleExclusion_of_inspections rankTwoInspectionAt otherInspectionAt

/-- The literal original point-control consumer with quasisimple exclusion discharged. -/
theorem pointControl_of_remaining_source_inputs
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hconstrained : ConstrainedExclusionAt T) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect quasisimpleExclusionAt hconstrained

/-- Selected source modules feed the direct rank-one point calculation and
all completed quasisimple comparisons. The remaining premises have external owners. -/
theorem pointControl_of_module_choice
    (hchoice : Selection.ModuleChoiceAt T)
    (hN : HalfUniqueness.StabilizerNormalizerAt T)
    (hhalf : HalfSylowUniqueAt T) (hconstrained : ConstrainedExclusionAt T) :
    SourceNonnormalPointControlAt T :=
  pointControl_of_remaining_source_inputs hhalf
    (Selection.ModuleChoice.selectionAt_of_module_choice_direct hchoice hN) hconstrained

/-- Fixed support supplies module choice on the same ambient group and Sylow.
The original normalizer, half-Sylow and constrained source obligations remain explicit. -/
theorem pointControl_of_fixed_support_rows
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hrows : Selection.ModuleChoice.FixedSupportRowsAt T)
    (hN : HalfUniqueness.StabilizerNormalizerAt T)
    (hhalf : HalfSylowUniqueAt T) (hconstrained : ConstrainedExclusionAt T) :
    SourceNonnormalPointControlAt T :=
  pointControl_of_module_choice
    (Selection.ModuleChoice.moduleChoiceAt_of_fixed_support_rows hG hrows) hN hhalf hconstrained
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
