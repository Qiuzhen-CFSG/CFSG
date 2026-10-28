module

public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.Centralizer
public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.Normalizer
public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.SylowNormalization
public import Stellmacher.Recognition.Parrott.LocalGenerators
public import Stellmacher.Recognition.Parrott.LocalInputs

/-!
# Parrott generators from local inputs: Complete

The normalized Sylow construction, centralizer extension, and compatible
normalizer normalization compose on the same supplied data. The resulting
dependent pair includes all elementary bases, the generation equalities for
J, T, H and N, and every equation (1)–(26). The separate braid relation and
ambient generation are not premises of this construction.

The derived-core normalizer identity and local normalizer solvability in
`ParrottLocalInputs` replace the ambient N₂ assumption. The original APIs
remain unchanged, and F, the supplied Sylow subgroup, t and v remain literal.

Source: D. Parrott, *A characterization of the Tits simple group* (1972),
§3, printed pp.678–682, with the local geometry of §§1–2.
-/

section

/- LocalGenerators: local-input version of the original construction. -/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Extend the supplied normalizer-fusion configuration to compatible local
generators satisfying all source equations (1)–(26). The elementary bases and
generation of the actual J,T,H,N are fields of this same pair of frames. -/
public theorem ParrottNormalizerFusionData.exists_local_generators_of_local_inputs
    [Finite G] [IsSimpleGroup G] (n : ParrottNormalizerFusionData e)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (Σ f : ParrottCentralizerGeneratorData n, ParrottNormalizerGeneratorData f) := by
  obtain ⟨f⟩ := n.exists_sylow_generators_of_local_inputs hns hlocal h
  obtain ⟨f'⟩ := f.exists_centralizer_generators_of_local_inputs hns hlocal h
  exact f'.nonempty_compatible_generator_data_of_local_inputs hns hlocal h

end Stellmacher.Recognition

end
