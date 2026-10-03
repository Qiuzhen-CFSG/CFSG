module

public import Stellmacher.Recognition.Parrott.CentralizerCompatibleDiscrepancy
public import Stellmacher.Recognition.Parrott.CentralizerFiniteActionFamily
public import Stellmacher.Recognition.Parrott.CentralizerCompatibleParameterExistence

/-!
# Classification of the compatible centralizer action

The actual Sylow commutators, involutivity, and the relation (ry)^5 = 1
give the corrected four-parameter family. The derived-subgroup discrepancy
then excludes the false first parameter. Combining these results gives
the true-α family on the supplied involution and Sylow frame, retaining
the elementary subgroup and normalizer data literally.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–681. The c-image uses the coefficient α xor β forced by
the core commutators.
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The compatible action on the supplied frame has first parameter true
under the original finite nonsolvable simple N₂ hypotheses. -/
public theorem ParrottCentralizerInvolutionData.exists_true_compatible_action_parameters
    [Finite G] [IsSimpleGroup G] (g : ParrottCentralizerInvolutionData n)
    (_hns : ¬ Group.IsSolvable G) (_hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ β δ γ : Bool, g.HasCompatibleActionParameters true β δ γ := by
  exact g.exists_true_compatible_action_parameters_of_exists h
    (g.exists_compatible_action_parameters h)

end Stellmacher.Recognition
