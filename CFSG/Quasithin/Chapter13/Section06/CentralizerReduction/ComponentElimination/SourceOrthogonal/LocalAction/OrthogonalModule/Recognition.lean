module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Extension
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Model

/-!
# Recognition reductions for the orthogonal moved section

The literal moved and central spaces retain the whole plus action.
Preparation applies the complete, projective-line-corrected B.5.1 input to
the actual component action, deriving faithfulness, offender generation and
the SQTK hypotheses. Extension promotes chosen A₈ coordinates to the whole
plus actor, using the natural module's trivial linear centralizer. The model
comparison then gives full equivariance in the retained orthogonal six-space.

These reductions retain component recognition as an explicit premise.
The downstream `Recognition.Source` module constructs that recognition
from the genuine earlier configuration, all three conclusions of 13.6.23
and the universal corrected B.5.1 implication. It discharges the ordinary
component FF assertion and every competing alternative before applying
these reductions to the actual orthogonal-model consumer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
following 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
open ComponentSelection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- Apply the explicit natural/orthogonal model comparison after promoting
component coordinates to the entire plus action. The original quotient and
the fixed kernel are unchanged. Component recognition remains an input. -/
theorem orthogonalCoordinates_of_component_natural
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (hnatural : IsAlternatingNatural
      (s.action.comp (plusImage K L T z v hL hz K).subtype) 8) :
    ∃ d : NaturalMovedSection K L T z v hL hz,
      Module.finrank (ZMod 2) (d.upper.toSubmodule ⧸ d.central.toSubmodule) = 6 ∧
      ∀ g w, d.orthogonalCoordinates K L T z v hL hz (d.central.quotientRepresentation g w) =
        (Atlas.Order20160A8.DeletedEight.orthogonalHom (d.actor g)).val
          (d.orthogonalCoordinates K L T z v hL hz w) := by
  obtain ⟨d⟩ := naturalMovedSection_of_component_natural K L T z v hL hz
    hK hLK hT hcore hout s hnatural
  exact ⟨d, d.section_finrank K L T z v hL hz,
    d.orthogonal_equivariant K L T z v hL hz⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
