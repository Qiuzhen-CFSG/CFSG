module

public import Theory.SpecificGroups.Alternating.SevenFiveCover

/-!
# The five-letter cover seed in the original A₇ assembly

Re-export the actual perfect-residual lift and its original-projection
formula. Chapter C uses the underlying Theory module directly, while the
Chapter 13 assembly retains this source interface.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingIntrinsic
export Theory.SpecificGroups.Alternating.SevenFiveCover
  (fiveLift fiveLift_perfect fiveLift_map fiveLiftMap fiveLiftMap_surjective
    fiveLiftMap_injective fiveLiftEquiv fiveLiftEquiv_apply
    fiveLiftEquivOfCentralQuotient fiveLiftEquivOfCentralQuotient_apply
    two_subgroup_le_fiveLift normalizes_fiveLift_of_map)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingIntrinsic
