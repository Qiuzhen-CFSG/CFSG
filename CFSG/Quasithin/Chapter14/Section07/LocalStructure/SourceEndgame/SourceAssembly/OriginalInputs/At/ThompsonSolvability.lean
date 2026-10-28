module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.SourceSolvability
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.PointCommutator

/-!
# Solvability of the actual Thompson subgroup from local source modules

The literal R₁ is Sylow in DR₁. The rank-one constituent classification
leaves a natural SL₂ section; faithful-family recognition makes its actor
A₅. Original 13.3.2(3) at G,T,L supplies a chosen A₅ constituent in the
moved span, contradicting the checked cubic fixed-vector calculation.
Thus J(DR₁) is solvable. No structural or universal module theorem is used.
The faithful and original A₅ inputs retain their existing producers, with
final assembly in qt-d-14775-source. Source: AS 14.7.67(4), p.1070.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer ResidualNormalizer.Components
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)
include d in
/-- The actual Thompson subgroup has no C-component. The only retained
module input is the genuine earlier 13.3.2 alternating-five implication. -/
theorem residual_thompson_no_component_of_original_modules_at
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) : False := by
  let hs := d.Ri_isSylowIn_D_sup_Ri
  let := (d.residualSpan_reduced hs).elementary
  obtain ⟨c⟩ := d.residual_global_component_classification earlier hs hB
  obtain ⟨k,⟨e⟩⟩ := d.residualGlobalComponent_linearTwo earlier hs hB c
  have hfive := d.residual_component_five_of_linearTwo earlier hs hB k e.groupEquiv
  obtain ⟨U,⟨chosen⟩,hUE⟩ := d.residual_component_chosen_in_moved_span earlier hs hB
  have hm := modules (Chapter14.Section03.FaithfulSource.hypothesis1331 d.counterexample)
    B (d.residual_component_faithful hs hB) hfive U chosen
  have hBE : B ≤ normalizer (E F : Set G) :=
    (hB.1.trans J_le_Y).trans d.residual_Y_normalizes_E
  exact d.residual_global_no_linearTwo_of_constituent earlier hs hB
    (hUE.trans (le_normalizer_iff_commutator_le_left.mp hBE)) hm c.sectionData k ⟨e⟩

include d in
/-- Solvability in 14.7.67 is constructed from the original component and
constituent classification, without a decomposition or solvability premise. -/
theorem residual_thompson_solvable_of_original_modules_at
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    Group.IsSolvable (J L F) := by
  by_contra hn
  obtain ⟨B,hB⟩ := exists_isCComponent_of_not_isSolvable hn
  apply d.residual_thompson_no_component_of_original_modules_at earlier modules
    (B := B.map (J L F).subtype)
  refine ⟨map_subtype_le B,?_⟩
  have he : (B.map (J L F).subtype).subgroupOf (J L F) = B :=
    comap_map_eq_self_of_injective (J L F).subtype_injective B
  rwa [he]

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
