module

public import Stellmacher.Recognition.Parrott.CentralizerActionData
public import Stellmacher.Recognition.Parrott.CentralizerInvolutionSeed
public import Stellmacher.Recognition.Parrott.CentralizerElementarySelection
public import Stellmacher.Recognition.Parrott.SylowYFusion

/-!
# Construction of Parrott's centralizer involution

The seed module constructs an actual outer involution generating the
centralizer with the supplied Sylow subgroup and satisfying the fifth-power
relation. It also completes equation (22) from (20)–(21), with every inherited
Sylow-frame field retained. Its public reductions are re-exported here.

The elementary-action selection supplies compatible images of t and v.
The normalized y belongs to the global class of z, so the fifth-power
relation places the selected involution in that class too. Combining these
results with the seed assembly gives every field of the involution stage,
retaining the supplied second elementary and normalizer-fusion data.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–681, especially the centralizer-generator paragraph through (22).
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Extend a complete normalized Sylow frame to an actual centralizer
involution satisfying equations (20)–(22). The supplied elementary subgroup
and normalizer-fusion data, hence F, T, z, t and v, are retained literally. -/
public theorem ParrottSylowGeneratorData.exists_centralizer_involution
    (f : ParrottSylowGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottCentralizerInvolutionData n) := by
  obtain ⟨f', r, hrH, hrT, hr2, hry, ht, hv⟩ :=
    f.exists_outer_involution_elementary_action hns hN h
  exact f'.centralizer_involution_of_t_v_conj h (f'.y_isConj_z hns hN h)
    r hrH hrT hr2 hry ht hv

end Stellmacher.Recognition
