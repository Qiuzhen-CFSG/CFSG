module

public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.Assembly
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.KnownSimpleSource
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.FullSource

/-!
# Ambient and B.5 discharge in the original 15.3 endgame

The original definite plane has order four and lies in the two-core of
the generated source group. This group therefore lies in the two-local
normalizer of a nontrivial two-group. The ambient simple QTKE hypotheses
supply SQTK for that normalizer and hence for the actual source subgroup.

The terminal application also instantiates the proved corrected B.5 source
classification. The genuine earlier geometry, descent, 68(2) centrality,
enumerated fusion input and corrected F.6 source classification remain
explicit. The final consumer propagates the corrected ambient dihedral
and square-field alternatives through the proved source intersection;
no legacy classifier or new recognition premise is introduced.

Source: Aschbacher--Smith, final proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource
open TerminalRecognition
open AbelianAmalgam.LocalStructure
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]
namespace SourceData
variable {T : Sylow 2 G} {M Mc P E : Subgroup G} {s : G}
  (d : SourceData T M Mc P E s)

/-- SQTK on the literal generated source subgroup follows from its
nontrivial two-core and the original ambient hypotheses. -/
theorem sourceGroup_sqtk (d : SourceData T M Mc P E s)
    {K : GroupClass.{u}} (hG : IsSimpleQTKE K G) :
    IsSQTK K (sourceGroup T M Mc E s) := by
  let H := sourceGroup T M Mc E s
  have hcore : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hV : localModule T M = ⊥ := bot_unique
      (d.terminal.module_le_core.trans_eq he)
    have hP := bot_unique (d.earlier.plane_le.trans hV.le)
    have hc := d.earlier.plane_card
    rw [hP,card_bot] at hc
    omega
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hs := hG.twoLocal_sqtk
    (show IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) from
      ⟨H.pCoreIn 2,hcore,isPGroup_pCoreIn 2 H,rfl⟩)
  exact ⟨hs.stronglyQuasithin.of_injective (inclusion hn) (inclusion_injective hn),
    hs.isKGroup.of_injective (inclusion hn) (inclusion_injective hn)⟩

/-- The original source endgame with its SQTK and B.5 premises discharged
on the same source subgroup and literal offender action. -/
theorem terminal_contradiction_knownSimple
    (d : SourceData T M Mc P E s)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (f : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    (classificationF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple) : False := by
  let _ := standard_elementary d.earlier.natural
  let k := d.coordinateModel
  let g := d.earlierGeometry k
  have h := SourceControls.controls_of_earlier_fusion_inputs k g f d.source_definite
    d.terminal.support_M d.residual_escape
  exact terminal_contradiction_of_source_ambient_span g h (d.sourceGroup_sqtk hG)
    classificationF Intersection.sourceFFClassification_knownSimple d.seed_le_original d.source_span

end SourceData
end CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource
