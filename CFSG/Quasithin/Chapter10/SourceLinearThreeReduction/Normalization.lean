module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction
public import CFSG.Quasithin.Chapter10.SourceNormalizationAssembly

/-!
# Normalization application of the non-A5 source reduction

The actual guarded normalization consumer takes the survivor constructed
from point control, the generation bound and small-offender recognition.
These source inputs, A5 tensor exclusion and the replacement theorem remain
explicit. The lower survivor module does not import normalization, so its
unconditional completion can later be imported by the assembly owner.

Source: Aschbacher--Smith 10.0.1 and the end of §10.3,
combined manuscript of 1 March 2004, printed pp.741,756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original multiple-overgroup normalization consumer, with the
non-A5 survivor obligation reduced to its three source producers. -/
theorem source_normalizes_of_nonnormal_source_inputs_of_many
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : SourceA5TensorExclusionAt T)
    (hpoint : SourceNonnormalPointControlAt T)
    (hgeneration : SourceNonnormalGenerationBoundAt T)
    (hsmall : SourceNonnormalSmallOffenderAt T)
    (hreplacement : SourceLinearThreeReplacementAt T)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) :=
  source_normalizes_of_source_branches_of_many hG hmany htensor
    (source_nonnormalReduction_of_point_generation_smallOffender hpoint hgeneration hsmall)
    hreplacement hL hf hq


end CFSG.Quasithin.Chapter10
