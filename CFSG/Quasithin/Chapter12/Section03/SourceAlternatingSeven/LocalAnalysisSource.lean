module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowNormalizer
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceConclusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Intersections

/-!
# The complete local A₇ analysis of 12.3.3–8

The four-dimensional exclusion and cohomological lift mark the entire original
chosen module V. The natural action supplies the Sylow-normalizer containment
and hence ambient fusion control. Applying the natural-coordinate theorem
uniformly to every other proposed A₇ component discharges the last premise of
the two ambient point-centralizer arguments. These results construct the
original LocalAnalysis, with its action through the original O₂,Z quotient.

The intersection and escaping-point applications below supply the local input
to the remaining weak-closure and terminal arguments of 12.3.1. Only structural
12.2.2, its seven-module classification, and the uniform centralizer escape
remain as the authorized earlier-source inputs. The original 12.3.7 Thompson
and omega-center conclusions are re-exported with the point-centralizer proof.

Source: Aschbacher–Smith, 12.3.3–8, printed pp.807–810; the applications are
12.3.9(1), p.810, and the escaping-point selection on p.811. Final exclusion
assembly belongs to qt-d-1231-source.
-/

@[expose] public noncomputable section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

/-- Original 12.3.3–8 on the chosen V, with all local-analysis premises
discharged from the permitted earlier-source inputs. -/
def localAnalysis
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : S.LocalAnalysis :=
  let E := S.naturalCoordinates structural modules escape
  E.localAnalysis structural (E.sylow_normalizer_le_component structural)
    (E.source_point_centralizer structural modules escape
      (fun _ _ SA => SA.naturalCoordinates_nonempty structural modules escape))

/-- Every proposed A₇ setup has the full natural action, ambient fusion
control, and ambient weight-two and weight-six centralizer bounds. -/
theorem localAnalysis_nonempty
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : Nonempty S.LocalAnalysis :=
  ⟨S.localAnalysis structural modules escape⟩

/-- The intersection consumer 12.3.9(1), now with its local-analysis input
constructed on the original chosen module. -/
theorem intersection_weight_four_of_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    {g x : G} (hg : g ∉ normalizer (V : Set G))
    (hx : x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom) (hx1 : x ≠ 1) :
    weight ((S.localAnalysis structural modules escape).model.coordinates
      ⟨x, hx.1⟩).toAdd.val = 4 :=
  intersection_weight_four S (S.localAnalysis structural modules escape)
    structural hg hx hx1

/-- The terminal source argument can choose its weight-four escaping point
without any additional natural-coordinate or point-centralizer premise. -/
theorem weight_four_escape_of_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ∃ v : V, v ≠ 1 ∧
      weight ((S.localAnalysis structural modules escape).model.coordinates v).toAdd.val = 4 ∧
      ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  weight_four_escape S (S.localAnalysis structural modules escape)
    (escape L V S.hypothesis S.chosen)

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
