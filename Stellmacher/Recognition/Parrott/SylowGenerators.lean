module

public import Stellmacher.Recognition.Parrott.LocalGeneratorData
public import Stellmacher.Recognition.Parrott.SylowSeedConstruction
public import Stellmacher.Recognition.Parrott.SylowSeedNormalization
public import Stellmacher.Recognition.Parrott.SylowOuterNormalization

/-!
# Normalizing Parrott's Sylow generators

The local geometry constructs a Sylow seed in one of the two printed cases.
The Case 2 change of coordinates, followed by conjugation, preserves the actual
subgroups and the supplied z,t,v while giving the unprimed seed equations.
Outer-generator normalization then completes equations (16)–(19). Together
these constructions give a normalized Sylow frame from the original recognition
hypotheses, retaining the actual E,F,J,T throughout.

Source: Parrott (1972), §3, pp.678–680.
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
variable {z : G} {e : ParrottSecondElementaryData z}

/-- The supplied normalizer data admit normalized Sylow generators satisfying
the unprimed equations (1)–(19), with z,t,v and the actual E,F,J,T preserved. -/
public theorem ParrottNormalizerFusionData.exists_sylow_generators
    (n : ParrottNormalizerFusionData e) (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottSylowGeneratorData n) := by
  obtain ⟨caseTwo, ⟨f⟩⟩ := n.exists_sylow_seed hns hN h
  exact f.normalize.exists_generators_of_seed hns hN h

end Stellmacher.Recognition
