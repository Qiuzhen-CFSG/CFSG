module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Generation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.BinaryOrbit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Assembly

/-!
# Conditional assembly of the replacement overgroup identity

The wreath radical and original component-orbit identities put K_z in the
actual M₊-span J_z. Strictness excludes J_z=X. The source normal-closure
alternatives then supply a component generating J_z. Generation-one model
rows contradict escape from M by the original E.3.35 bound. In the binary
row the full-Sylow local embedding theorem identifies the component orbits.

The two earlier-source predicates remain explicit; neither is inferred
from a record projection. The original replacement assembly consumes the
resulting OvergroupSpanAt with no further overgroup premise.
Source: Aschbacher--Smith §10.3, final paragraph, pp.756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Final span assembly from the two independent earlier-source arguments. -/
theorem overgroupSpan_of_source_inputs
    (halternatives : ClosureAlternativesAt T)
    (hgeneration : ModelGenerationAt T) : OvergroupSpanAt T := by
  intro hmany L D s d he hstrict hout horbit M hM hJM
  obtain ⟨e⟩ := he
  have hle := componentSpan_le_overgroup_span d e hstrict horbit hJM
  rcases halternatives hmany L D s d ⟨e⟩ hstrict hout horbit M hM hJM with
    hsame | ⟨I,hI,hq,hgen,hmodel⟩
  · exact (hstrict.not_ge (hle.trans_eq hsame)).elim
  · rcases hgeneration hmany L D s d ⟨e⟩ hstrict hout horbit M hM hJM I hI hq hgen hmodel with
      ⟨n,hn⟩ | hOne
    · exact span_eq_of_binary_orbit d e hstrict horbit hM hJM hI hq hn hgen
    · have hsmall := le_maximal_of_eGenerated_one s d
        (H := componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G)) le_sup_right hOne
      apply (hout ?_).elim
      exact hle.trans ((hgen.le.trans le_sup_left).trans hsmall)

/-- Application to the original replacement consumer. Geometry and wreath
recognition still belong to their independent producers. -/
theorem replacement_of_geometry_wreath_and_source_inputs
    (hgeometry : CentralizerGeometryAt T) (hwreath : WreathRecognitionAt T)
    (halternatives : ClosureAlternativesAt T)
    (hgeneration : ModelGenerationAt T) : SourceLinearThreeReplacementAt T :=
  replacement_of_source_inputs hgeometry hwreath
    (overgroupSpan_of_source_inputs halternatives hgeneration)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
