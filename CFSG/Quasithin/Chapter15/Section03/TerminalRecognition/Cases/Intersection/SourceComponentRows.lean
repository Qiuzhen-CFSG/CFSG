module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceClassifications
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceComponentRows.OddFields
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceComponentRows.Covers
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceComponentRows.HighRows

/-!
# Terminal component comparison from corrected source witnesses

The full F.6.18 alternative, in either labeling, is compared with the
corrected B.5.6 action on the same offender subgroup. All thirteen rows
are discharged using the existing group calculations and the marked
G₂(2) action. The resulting two-group quotient gives the literal embedded
two-residual equality via the established residual-lifting theorem.
The original G₁ normalization and every public legacy interface are preserved.

The proofs adapt the existing terminal `ComponentRows` comparison to the
full `ProjectiveLine.QuasisimpleSourceConclusion`. The two-dimensional
F₄ offender clause remains on the original action; no legacy clause is
constructed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1/B.5.6,
printed pp.99–105; F.6.18, pp.309–310; K.1.3, p.453; final proof of
15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

private theorem source_component_rows_of_labeled_alternative
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup))
    {G₁ G₂ : Subgroup (coreQuotient H)}
    (hlabels : (G₁ = d.G1.map coreProjection ∧ G₂ = d.G2.map coreProjection) ∨
      (G₁ = d.G2.map coreProjection ∧ G₂ = d.G1.map coreProjection))
    (hF : FSource.Alternative G₁ G₂ d.quotientSylow) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  cases hF with
  | one _ hleft hright _ =>
    rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (d.first_quotient_core_ne_bot hleft).elim
    · exact (d.first_quotient_core_ne_bot hright).elim
  | two hmodel =>
    exact (ComponentRows.OffenderReduction.not_row_two hL hmodel).elim
  | three r _ _ _ =>
    exact (ComponentRows.OffenderReduction.not_productRow hL r).elim
  | four F hn hm e ht _ hs hleft hright =>
    apply (d.source_component_row_four_impossible hL c F hn hm e ht hs ?_).elim
    rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hleft, hright⟩
    · exact ⟨hright, hleft⟩
  | five F hn hm e eL _ hs hleft hright =>
    apply (d.source_component_row_five_impossible hL c F hn hm e eL hs ?_).elim
    rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hleft, hright⟩
    · exact Or.inr ⟨hleft, hright⟩
  | six hmodel ht _ hs hleft hright =>
    rcases hmodel with hcover | ⟨F, hn, hm, ⟨e⟩⟩
    · exact d.component_row_tripleSix hL ht hcover
    · apply d.source_component_row_six_pslTwo hL c F hn hm e ht hs
      rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hleft, hright⟩
      · exact ⟨hright, hleft⟩
  | seven hmodel _ _ _ _ =>
    rcases hmodel with he | hcover
    · obtain ⟨e⟩ := he
      exact d.component_row_alternatingSeven hL e
    · exact (d.source_component_row_tripleSeven_false hL c hcover).elim
  | eight hmodel _ hs hleft hright =>
    rcases hmodel with hcover | hr
    · obtain ⟨hcover⟩ := hcover
      exact d.source_component_row_tripleSymmetricSix hL c hcover
    · obtain ⟨r⟩ := hr
      apply d.source_component_row_eight_field hL c r hs
      rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hleft, hright⟩
      · exact ⟨hright, hleft⟩
  | nine hmodel _ _ _ _ =>
    rcases hmodel with he | hcover
    · obtain ⟨e⟩ := he
      exact d.component_row_symmetricSeven hL e
    · obtain ⟨hcover⟩ := hcover
      exact (d.source_component_row_tripleSymmetricSeven_false hL c hcover).elim
  | ten _ hp hm hdegree ht _ hs _ _ =>
    exact (d.source_component_row_ten_false hL c hp hm hdegree ht hs).elim
  | eleven r _ hs _ _ =>
    exact d.source_component_row_eleven hL c r hs
  | twelve e _ _ _ _ =>
    exact (d.source_component_row_twelve_false hL c e).elim
  | thirteen _ eL _ _ _ _ =>
    exact (d.source_component_row_thirteen_false hL c eL).elim

/-- The quasisimple ambient-component branch of the terminal intersection.
Both F.6.18 labelings use the same source input and full offender action;
the quasisimple B-side witness is obtained from the given B.5.6 alternative. -/
theorem source_component_rows_of_classifications
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  obtain ⟨c⟩ := d.source_offender_quasisimple_of_classifications hL hB
  rcases hF with hF | hF
  · exact d.source_component_rows_of_labeled_alternative hL c (Or.inl ⟨rfl, rfl⟩) hF
  · exact d.source_component_rows_of_labeled_alternative hL c (Or.inr ⟨rfl, rfl⟩) hF

/-- The quotient conclusion discharges the embedded residual equality used
in the next paragraph of the source proof, on the original subgroup J(H). -/
theorem source_component_intersection_of_classifications
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H := by
  obtain ⟨hX, hD, hquot⟩ := d.source_component_rows_of_classifications hL hF hB
  exact ⟨hX, hD, d.residual_eq_of_fitting_quotient hL hquot⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
