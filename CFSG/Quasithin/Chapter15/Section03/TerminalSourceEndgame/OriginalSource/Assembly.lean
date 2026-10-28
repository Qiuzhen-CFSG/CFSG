module

public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.ActionComparison
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.Intrinsic
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Applying the terminal contradiction to original source data

The intrinsic terminal input and ambient geometry are constructed on the same
subgroups, coordinates, conjugating element and marked singular four-group.
The source span is converted by inverse reindexing inside its actual actor.
The resulting theorem applies SourceControls.terminal_contradiction_from_earlier_fusion;
the elementary-module instance comes from the original coordinates.

The genuine earlier local/descent data, 68(2) centrality, enumerated fusion
inputs, SQTK hypothesis and full universal F.6.18/B.5.6 classifications remain
with their existing source producers. No terminal recognized model or definite
plane normalizer is an additional premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
proof of Theorem 15.3.1, printed p.1155 (PDF p.1172).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource

open Subgroup Stellmacher AbelianAmalgam TerminalRecognition
open TerminalRecognition.ExceptionalAction
open scoped IsMulCommutative Pointwise

universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Right-conjugate and conjugate-closure conventions generate the same span,
using inverse reindexing inside the very same acting subgroup. -/
theorem source_span_eq (Y Z : Subgroup G) :
    GoldschmidtCore.ThompsonExtension.conjugateSpan Y Z = conjugateSpanBy Z Y := by
  rw [GoldschmidtCore.ThompsonExtension.conjugateSpan, conjugateSpanBy_eq_iSup_conj]
  apply le_antisymm
  · apply iSup_le
    intro y
    exact le_iSup (fun x : Y => Z.map (MulAut.conj (x : G)).toMonoidHom) y⁻¹
  · apply iSup_le
    intro y
    simpa only [Subgroup.coe_inv, inv_inv] using
      (le_iSup (fun x : Y => Z.map (MulAut.conj (x : G)⁻¹).toMonoidHom) y⁻¹)

namespace SourceData

variable {T : Sylow 2 G} {M Mc P E : Subgroup G} {s : G}
  (d : SourceData T M Mc P E s)
variable [IsElementaryAbelian 2 (localModule T M)]
include d

local notation "V" => localModule T M
local notation "Y" => residualY M Mc
local notation "F₀" => otherLine E s
local notation "H" => sourceGroup T M Mc E s

theorem source_definite : FusionCore.IsDefinitePlane
    (quadraticAction d.earlier.natural).form P :=
  definite_of_standard d.earlier.natural d.earlier.plane_le d.earlier.plane_card
    d.earlier.plane_definite

/-- Actual coordinate comparison supplied by the public wreath theorem. -/
noncomputable def coordinateModel :
    FusionCore.OrthogonalCoordinateModel (quadraticAction d.earlier.natural) P :=
  Classical.choice (coordinates_from_standard d.earlier.natural d.source_definite)

/-- The ambient geometry is aligned by the original subgroup inclusion and
original conjugator; the selected intrinsic groups are those of sourceInput. -/
noncomputable def earlierGeometry
    (k : FusionCore.OrthogonalCoordinateModel (quadraticAction d.earlier.natural) P) :
    EarlierGeometry k.action d.sourceInput where
  T := T
  Mc := Mc
  E := E
  s := s
  sylow_le := d.sylow_le
  vector_eq := rfl
  singular_card := d.earlier.line_card
  singular := by
    apply SourceControls.singularIn_of_totallySingular k
    refine ⟨d.earlier.line_le, ?_⟩
    intro v hv
    exact d.earlier.line_singular ⟨v, hv⟩
  sylow_map := d.sourceSylow_map
  first_map := (map_subgroupOf_eq_of_le (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).trans d.conjugate_residual
  second_map := map_subgroupOf_eq_of_le (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))
  singular_map := map_subgroupOf_eq_of_le d.singular_le_group
  conjugator_mem := conjugator_preserves_first_plane k d.sylow_le d.conjugator_mem
  conjugator_not_mem := d.conjugator_outside
  residual_image := residual_image_of_standard d.earlier.natural k.action Y d.earlier.residual_image
  ambient_product := d.ambient_product
  residual_product := by
    rw [← d.conjugate_residual]
    exact d.terminal.product_Y
  residual_normalized := d.terminal.normalizes_lineY
  residual_core_le := d.earlier.residual_core_module.le.trans inf_le_right
  centralizer_le := d.centralizer_le_common
  first_commutator := d.original_vector_commutator

omit [IsElementaryAbelian 2 (localModule T M)] in
theorem source_span : F₀ = conjugateSpanBy (centralInvolutions T)
    (otherLine (lineY Y E) s) := by
  rw [← d.conjugate_residual, ← source_span_eq]
  exact d.terminal.seed_span

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- Actual-source terminal application of 15.3.1. The unfinished earlier
source implications are precisely SourceData's genuine 68(2)/descent
inputs, the enumerated fusion input, and the full universal classifiers. -/
theorem terminal_contradiction
    (f : FusionCore.EarlierFusionInputs T M V P)
    {K : GroupClass.{u}} (hH : IsSQTK K H)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K) : False := by
  exact SourceControls.terminal_contradiction_from_earlier_fusion
    d.coordinateModel (d.earlierGeometry d.coordinateModel) f d.source_definite
    d.terminal.support_M d.residual_escape hH classificationF classificationB
    d.seed_le_original d.source_span

omit [IsElementaryAbelian 2 (localModule T M)] in
/-- The source coordinates discharge even the elementary-module instance
in the final application. All remaining hypotheses are actual earlier
source inputs, with no coordinate or recognized-model premise. -/
theorem terminal_contradiction_from_source
    (f : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    {K : GroupClass.{u}} (hH : IsSQTK K (sourceGroup T M Mc E s))
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K) : False := by
  let _ := standard_elementary d.earlier.natural
  exact d.terminal_contradiction f hH classificationF classificationB

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

omit [IsElementaryAbelian 2 (localModule T M)] in
/-- The same actual-source endgame takes the full corrected universal B.5.6
classification, retaining all of its projective-line action conclusions. -/
theorem terminal_contradiction_of_full_classifications
    (f : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    {K : GroupClass.{u}} (hH : IsSQTK K (sourceGroup T M Mc E s))
    (classificationF : FSource.ClassificationInput K)
    (classificationB : FFAlternatives.ProjectiveLine.CompleteClassificationInput.{u,u} K) :
    False := by
  refine d.terminal_contradiction_from_source f hH classificationF ?_
  intro D _ _ W _ _ ρ h
  exact Or.inl (classificationB.general D W ρ h)

end SourceData
end CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource
