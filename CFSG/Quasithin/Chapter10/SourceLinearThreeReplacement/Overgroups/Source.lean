module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Source

/-!
# The replacement overgroup span and its source consumers

For every maximal two-local M₊ containing K_zT, the original seed
X = O²(C_{L₀}(z)) has M₊-normal closure exactly K_z. The completed closure
alternatives and model-generation calculation discharge both inputs to
the span assembly. Generation one excludes the nonbinary rows, including
Held; the full-Sylow rank-one embedding argument identifies the remaining
component orbit with K_z.

The literal replacement consumer consequently needs only the earlier
centralizer geometry and wreath recognition. Their discharge belongs to
`qt-d-10-replacement-centralizer-geometry` and
`qt-d-10-replacement-wreath-recognition`; final replacement assembly stays
with `qt-d-10-linear-three-replacement`. The normalization application also
retains its independent tensor and survivor-reduction inputs, whose final
assembly belongs to `qt-d-1222-normalization`.

Source: Aschbacher--Smith §10.3, final paragraph, pp.756--757,
using 10.2.4 and the rank-one exclusion of A.3.14.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The exact original overgroup-span contract, with the closure and
model-generation arguments fully discharged. -/
theorem overgroupSpan (T : Sylow 2 G) : OvergroupSpanAt T :=
  overgroupSpan_of_source_inputs (Closure.closureAlternatives T)
    (ModelGeneration.modelGeneration T)

/-- Construct the actual faithful maximal A₅ replacement from the two
remaining earlier-source inputs, on the original group and Sylow subgroup. -/
theorem replacement_of_geometry_and_wreath
    (hgeometry : CentralizerGeometryAt T) (hwreath : WreathRecognitionAt T) :
    SourceLinearThreeReplacementAt T :=
  replacement_of_source_inputs hgeometry hwreath (overgroupSpan T)

/-- Apply the completed span calculation in the literal normalization
consumer; no overgroup-span or model-generation callback remains. -/
theorem normalizes_of_geometry_and_wreath
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : SourceA5TensorExclusionAt T)
    (hreduction : SourceNonnormalReductionAt T)
    (hgeometry : CentralizerGeometryAt T) (hwreath : WreathRecognitionAt T)
    {L : Subgroup G} (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) :=
  source_normalizes_of_source_branches_of_many hG hmany htensor hreduction
    (replacement_of_geometry_and_wreath hgeometry hwreath) hL hf hq

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
