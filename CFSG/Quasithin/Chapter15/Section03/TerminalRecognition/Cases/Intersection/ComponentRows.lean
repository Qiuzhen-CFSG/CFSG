module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Actors
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Models
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Basic
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Permutation
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Actions
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.OddFields
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.OffenderReduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.TripleRows

/-!
# Quasisimple ambient-component rows of the terminal intersection

Assuming the ambient generalized Fitting subgroup is quasisimple, the
B-side reduction produces the full quasisimple action witness on the
actual offender group. We then exhaust all thirteen F.6.18 rows using
the odd-field, covered permutation, degree-three and Mathieu comparisons.
The surviving Thompson and ambient models carry actual isomorphisms or
central covering witnesses, and the quotient over the ambient component
is a two-group. This also proves the equality of the embedded two-residuals
of J(H) and H needed in the next paragraph of the source proof.

Both possible local labelings are handled without changing `SourceInput`
or its normalization of J(T_E) by the original G₁. The Thompson, offender
and ambient actors remain distinct until their equality is proved in a
particular row. The two classification conclusions remain explicit inputs;
no additional component witness, rank bound or residual identity is assumed.
The enclosing `Intersection` module owns combination with the low-row branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
final proof of 15.3.1, printed p.1155; F.6.18, pp.309–310;
B.5.1 and B.5.6, pp.99–105.
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

private theorem component_rows_of_labeled_alternative
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : FFAlternatives.QuasisimpleSourceConclusion d.offenderAction
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
    apply (d.component_row_four_impossible hL c F hn hm e ht hs ?_).elim
    rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hleft, hright⟩
    · exact ⟨hright, hleft⟩
  | five F hn hm e eL _ hs hleft hright =>
    apply (d.component_row_five_impossible hL c F hn hm e eL hs ?_).elim
    rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hleft, hright⟩
    · exact Or.inr ⟨hleft, hright⟩
  | six hmodel ht _ hs hleft hright =>
    rcases hmodel with hcover | ⟨F, hn, hm, ⟨e⟩⟩
    · exact d.component_row_tripleSix hL ht hcover
    · apply d.component_row_six_pslTwo hL c F hn hm e ht hs
      rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hleft, hright⟩
      · exact ⟨hright, hleft⟩
  | seven hmodel _ _ _ _ =>
    rcases hmodel with he | hcover
    · obtain ⟨e⟩ := he
      exact d.component_row_alternatingSeven hL e
    · exact (d.component_row_tripleSeven_false hL c hcover).elim
  | eight hmodel _ hs hleft hright =>
    rcases hmodel with hcover | hr
    · obtain ⟨hcover⟩ := hcover
      exact d.component_row_tripleSymmetricSix hL c hcover
    · obtain ⟨r⟩ := hr
      apply d.component_row_eight_field hL c r hs
      rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hleft, hright⟩
      · exact ⟨hright, hleft⟩
  | nine hmodel _ _ _ _ =>
    rcases hmodel with he | hcover
    · obtain ⟨e⟩ := he
      exact d.component_row_symmetricSeven hL e
    · obtain ⟨hcover⟩ := hcover
      exact (d.component_row_tripleSymmetricSeven_false hL c hcover).elim
  | ten _ hp hm hdegree ht _ hs _ _ =>
    exact (d.component_row_ten_false hL c hp hm hdegree ht hs).elim
  | eleven r _ hs _ _ =>
    exact d.component_row_eleven hL c r hs
  | twelve e _ _ _ _ =>
    exact (d.component_row_twelve_false hL c e).elim
  | thirteen _ eL _ _ _ _ =>
    exact (d.component_row_thirteen_false hL c eL).elim

/-- The quasisimple ambient-component branch of the terminal intersection.
Both F.6.18 labelings use the same source input and full offender action;
the quasisimple B-side witness is obtained from the given B.5.6 alternative. -/
theorem component_rows_of_classifications
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : FFAlternatives.SourceAlternative d.offenderAction) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  obtain ⟨c⟩ := d.offender_quasisimple_source_of_sourceAlternative hL hB
  rcases hF with hF | hF
  · exact d.component_rows_of_labeled_alternative hL c (Or.inl ⟨rfl, rfl⟩) hF
  · exact d.component_rows_of_labeled_alternative hL c (Or.inr ⟨rfl, rfl⟩) hF

/-- The quotient conclusion discharges the embedded residual equality used
in the next paragraph of the source proof, on the original subgroup J(H). -/
theorem component_intersection_of_classifications
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : FFAlternatives.SourceAlternative d.offenderAction) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H := by
  obtain ⟨hX, hD, hquot⟩ := d.component_rows_of_classifications hL hF hB
  exact ⟨hX, hD, d.residual_eq_of_fitting_quotient hL hquot⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
