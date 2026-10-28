module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.SurvivorGeometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Source

/-!
# The actual A₅ replacement for the linear-three survivor

The original natural action and point centralizers give the moved-factor TI
property after the fixed-part contradiction. This constructs the centralizer
geometry directly on the supplied survivor. The proved wreath theorem gives
an actual S₅ wr C₂ quotient of K_zT, and the overgroup span theorem promotes
its escaping A₅ component to a faithful maximal member of L(G,T).

All replacement inputs are discharged. The normalization consumer retains
only tensor exclusion and production of the original survivor, whose final
assembly belongs to `qt-d-1222-normalization`.

Source: Aschbacher--Smith, §10.3, printed pp.755--757, using 10.2.4 and
10.2.11. All quotients and subgroup inclusions are the literal source ones.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Construct an actual faithful maximal A₅ replacement from the original
linear-three survivor and multiple-overgroup guard. The ambient simple QTKE
hypothesis is supplied by its fundamental setup. -/
theorem source_linearThreeReplacement (T : Sylow 2 G) :
    SourceLinearThreeReplacementAt T :=
  SourceLinearThreeReplacement.replacement_of_source_inputs
    (SourceLinearThreeReplacement.centralizerGeometry T)
    (SourceLinearThreeReplacement.wreathRecognition T)
    (SourceLinearThreeReplacement.Overgroups.overgroupSpan T)

/-- Apply the completed replacement to the original Chapter 10 normalization
endgame. The independent tensor and non-A₅ survivor producers remain explicit. -/
theorem source_normalizes_after_linearThreeReplacement_of_many
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : SourceA5TensorExclusionAt T)
    (hreduction : SourceNonnormalReductionAt T)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) :=
  source_normalizes_of_source_branches_of_many hG hmany htensor hreduction
    (source_linearThreeReplacement T) hL hf hq

end CFSG.Quasithin.Chapter10
