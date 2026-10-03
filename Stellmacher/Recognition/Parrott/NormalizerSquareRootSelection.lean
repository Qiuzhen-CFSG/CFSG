module

public import Stellmacher.Recognition.Parrott.NormalizerTransportData
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionTransport
public import Stellmacher.Recognition.Parrott.NormalizerRootFiberCensus
public import Stellmacher.Recognition.Parrott.NormalizerGeneratorSeed

/-!
# Assembly of the normalizer square-root selection

The construction has two geometric steps: selecting the transport involution,
then normalizing its square-root orbit. The transport existence theorem now
discharges the first step from the recognition hypotheses. The remaining
conditional assembly retains the supplied centralizer frame literally and
requires only the square-root normalization theorem.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed pp.681–682, through the sixteen-root orbit paragraph.
-/

namespace Stellmacher.Recognition.ParrottCentralizerGeneratorData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Assemble transport and orbit normalization on the same supplied frame. -/
public theorem exists_normalizerSeed_of_transport_normalization
    (f : ParrottCentralizerGeneratorData n)
    (htransport : Nonempty (ParrottNormalizerTransportData f))
    (hnormalize : ParrottNormalizerTransportData f → Nonempty (ParrottNormalizerSeedData f)) :
    Nonempty (ParrottNormalizerSeedData f) := by
  obtain ⟨k⟩ := htransport
  exact hnormalize k

/-- The proved involution transport leaves only square-root normalization.
The normalization may replace the transport involution, but must retain the
literal supplied elementary subgroup, fusion witnesses and centralizer frame. -/
public theorem exists_normalizerSeed_of_normalization
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z)
    (hnormalize : ParrottNormalizerTransportData f → Nonempty (ParrottNormalizerSeedData f)) :
    Nonempty (ParrottNormalizerSeedData f) :=
  f.exists_normalizerSeed_of_transport_normalization
    (f.exists_normalizer_transport hns hN h) hnormalize

/-- The root-fiber census supplies the normalization for the transported
involution, completing the unconditional seed construction. -/
public theorem exists_normalizerSeed
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottNormalizerSeedData f) :=
  f.exists_normalizerSeed_of_normalization hns hN h
    (fun k => k.exists_seed h)

end Stellmacher.Recognition.ParrottCentralizerGeneratorData
