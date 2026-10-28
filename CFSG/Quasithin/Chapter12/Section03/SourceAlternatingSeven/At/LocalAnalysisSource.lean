module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.Intersections
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersTwoSourceConclusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowNormalizer

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
The versions in this extension require only `Structural1222At` and
`Theorem1222ModulesAt` at the original G,T. Every overcomponent is treated
in that same ambient group with that same Sylow subgroup. The original
universal declarations and all shared quotient/action records are preserved.
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

def localAnalysis_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : S.LocalAnalysis :=
  let E := S.naturalCoordinates_at structural modules escape
  E.localAnalysis_at structural (E.sylow_normalizer_le_component_at structural)
    (E.source_point_centralizer_at structural modules escape
      (fun _ _ SA => SA.naturalCoordinates_nonempty_at structural modules escape))

theorem localAnalysis_nonempty_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : Nonempty S.LocalAnalysis :=
  ⟨S.localAnalysis_at structural modules escape⟩

theorem intersection_weight_four_of_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    {g x : G} (hg : g ∉ normalizer (V : Set G))
    (hx : x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom) (hx1 : x ≠ 1) :
    weight ((S.localAnalysis_at structural modules escape).model.coordinates
      ⟨x, hx.1⟩).toAdd.val = 4 :=
  intersection_weight_four_at S (S.localAnalysis_at structural modules escape)
    structural hg hx hx1

theorem weight_four_escape_of_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    ∃ v : V, v ≠ 1 ∧
      weight ((S.localAnalysis_at structural modules escape).model.coordinates v).toAdd.val = 4 ∧
      ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  weight_four_escape_at S (S.localAnalysis_at structural modules escape)
    (escape L V S.hypothesis S.chosen)

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

