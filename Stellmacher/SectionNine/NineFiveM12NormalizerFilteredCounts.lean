module

public import Stellmacher.SectionNine.NineFiveM12NormalizerMaskReduction

@[expose] public section

namespace Stellmacher.SectionNine.M12Realization

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem normalizerLocalParameters_card : normalizerLocalParameters.card = 192 := by
  rw [normalizerLocalParameters_eq_maskParameters]
  decide +kernel

theorem normalizerIntersectionParameters_card :
    normalizerIntersectionParameters.card = 64 := by
  rw [normalizerIntersectionParameters_eq_maskParameters]
  decide +kernel

theorem normalizer_filtered_parameter_cardinals :
    normalizerLocalParameters.card = 192 ∧
      normalizerIntersectionParameters.card = 64 := by
  exact ⟨normalizerLocalParameters_card, normalizerIntersectionParameters_card⟩

end Stellmacher.SectionNine.M12Realization
