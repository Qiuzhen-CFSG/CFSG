module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.SourceMarked

/-!
# The four surviving terminal quotient models

The full marked F.6.18 rows are retained while applying the intersection.
The two S₄ locals exclude row (6) in either labeling. The A₇ dimension
obstruction excludes row (7); all other discarded rows have already been
excluded by the source intersection. Rows (8), (9) and (11) give S₆, Ŝ₆,
S₇ and G₂(2) through their actual equivalences or covering witnesses.

The triple-symmetric output retains its cubic kernel, symmetric quotient,
perfect triple-alternating derived subgroup and sign action. It does not
identify that cover with a concrete hexacode carrier before the independent
cover/action comparison. The FF witness remains on the original offender
subgroup throughout, including its projective-line convention.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.6.18,
printed pp.309–310; final proof of 15.3.1, printed p.1155, PDF p.1172.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

namespace Cases

/-- The four actual full quotients on p.1155. The hatted branch retains the
source covering and sign-action data for the later representation comparison. -/
inductive SurvivingQuotientAlternative (D : Type*) [Group D] : Prop
  | symmetricSix (equiv : D ≃* Equiv.Perm (Fin 6))
  | tripleSymmetricSix (cover : FSource.TripleSymmetric D 6)
  | symmetricSeven (equiv : D ≃* Equiv.Perm (Fin 7))
  | g2Two (equiv : D ≃* Atlas.G2.Model (ZMod 2))

end Cases

namespace Intersection.SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

private theorem source_survivors_of_labeled_alternative
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup))
    (hres : (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype =
      pResidual 2 H)
    {G₁ G₂ : Subgroup (coreQuotient H)}
    (hlabels : (G₁ = d.G1.map coreProjection ∧ G₂ = d.G2.map coreProjection) ∨
      (G₁ = d.G2.map coreProjection ∧ G₂ = d.G1.map coreProjection))
    (hF : FSource.Alternative G₁ G₂ d.quotientSylow) :
    Cases.SurvivingQuotientAlternative (coreQuotient H) := by
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
  | six _ _ _ _ hleft hright =>
    rcases hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (MarkedElimination.source_symmetricFour_quotient_excluded
        (d.toActionInput hres) hleft.some).elim
    · exact (MarkedElimination.source_symmetricFour_quotient_excluded
        (d.toActionInput hres) hright.some).elim
  | seven hmodel _ _ _ _ =>
    rcases hmodel with he | hcover
    · exact (Cases.source_alternatingSeven_excluded d hL c he.some).elim
    · exact (d.source_component_row_tripleSeven_false hL c hcover).elim
  | eight hmodel _ hs _ _ =>
    rcases hmodel with hcover | hr
    · exact .tripleSymmetricSix hcover.some
    · obtain ⟨r⟩ := hr
      have hp := d.source_component_row_eight_field_prime hL c r hs
      obtain ⟨e⟩ := ComponentRows.OddFields.fieldRow_nine_equiv_symmetricSix
        r hp d.quotientSylow hs.some
      exact .symmetricSix e
  | nine hmodel _ _ _ _ =>
    rcases hmodel with he | hcover
    · exact .symmetricSeven he.some
    · exact (d.source_component_row_tripleSymmetricSeven_false hL c hcover.some).elim
  | ten _ hp hm hdegree ht _ hs _ _ =>
    exact (d.source_component_row_ten_false hL c hp hm hdegree ht hs).elim
  | eleven r _ hs _ _ =>
    obtain ⟨⟨e⟩, _⟩ := d.source_component_row_eleven_ambient hL c r hs
    exact .g2Two e
  | twelve e _ _ _ _ =>
    exact (d.source_component_row_twelve_false hL c e).elim
  | thirteen _ eL _ _ _ _ =>
    exact (d.source_component_row_thirteen_false hL c eL).elim

/-- The source intersection and marked exclusions leave exactly the four
full quotients. The S₃-image exclusion is supplied by the preceding branch,
not inferred from a family tag; both F.6.18 labelings are handled. -/
theorem source_surviving_quotient_of_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃*
      Equiv.Perm (Fin 3))) :
    Cases.SurvivingQuotientAlternative (coreQuotient H) := by
  have hL : IsQuasisimple (generalizedFitting (coreQuotient H)) := by
    by_contra hL
    exact hnot (d.source_thompson_symmetricThree_of_nonquasisimple hF hB hL)
  obtain ⟨_, _, hres⟩ := d.source_nonS3_intersection_of_classifications hF hB hnot
  obtain ⟨c⟩ := d.source_offender_quasisimple_of_classifications hL hB
  rcases hF with hF | hF
  · exact d.source_survivors_of_labeled_alternative hL c hres (Or.inl ⟨rfl, rfl⟩) hF
  · exact d.source_survivors_of_labeled_alternative hL c hres (Or.inr ⟨rfl, rfl⟩) hF

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
