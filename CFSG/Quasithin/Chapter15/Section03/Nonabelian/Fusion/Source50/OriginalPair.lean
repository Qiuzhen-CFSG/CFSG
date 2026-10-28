module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalInitial
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.NonabelianBranch
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.Source
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.Center
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters.Literal
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.SourceSpan

/-!
# The marked pair from the original source hypotheses

The ordinary source kernel and the actual nonabelian U image supply the
movement hyperplane V∩U=V∩O₂(C_G(Z)). Applying the proved source54 construction
chooses one conjugator and one marked G.2.6 hypothesis. Its canonical source
module witness retains the common multiplicity for recognition and the later
layer actions. Source55 gives extraspecial U and the embedded center of P for
this same conjugator.

Source: Aschbacher–Smith, 15.3.54–55, printed pp.1146–1147.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open FusionCore.CosetSetup ChapterA.Section05To06
open ChapterG.Section02 OrthogonalPlusFour OrthogonalPlusFour.Chapter15Collapse
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
  (hempty : MainForward.faithfulLocalComponents d.T = ∅)
  (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
  (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
  (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
  (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
include hG hempty hM hu hmany

/-- The original residual spans the exact module used in the pair. -/
theorem original_residual_span : localSpan d.Z d.Y = d.V := by
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  exact source_residual_seed_span hG d.T hempty d.action hM hu hmany hne

include hfixed

/-- The source53 hyperplane is simultaneously the intersection with U and
with the actual involution-centralizer core. -/
theorem original_pair_hyperplane
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z))) :
    d.ZS ≤ d.V ⊓ closureU d.Z d.ZS ∧
      d.V ⊓ closureU d.Z d.ZS = d.V ⊓ coreQ d.Z := by
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hf := original_conjugates_centralize hG d hM hfixed
  have hab := original_U_nonabelian hG d hempty hM hu hmany hfixed hnon
  have hi := nonabelian_intersections d (centralizerH d.Z) h hf hnon hab
  exact ⟨le_inf h.plus_le (le_conjugateSpanBy _ _),hi.2.1.trans hi.1.symm⟩

/-- One marked G.2.6 witness and its canonical module data serve every
subsequent source54–58 consumer. All hypotheses come from the original
ambient setup and the contrary nonabelian V-span. -/
theorem original_pair_exists
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z))) :
    ∃ g ∈ d.Y, ∃ h26 : Hypothesis
        (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g,
      letI := moduleSectionNormal h26 h26.I_eq_LU
      letI := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
      ∃ f : SourceModuleData h26,
        f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity ∧
        (∀ v : (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T).VL,
          determinantForm (h26.coordinates v).toAdd =
            FusionCore.orthogonalCoordinateValue (d.action.coordinates
              ((MulEquiv.subgroupCongr (original_residual_span hG d hempty hM hu hmany)) v))) ∧
        IsExtraspecial 2 (closureU d.Z d.ZS) ∧
        center (closureU d.Z d.ZS) = d.Z.subgroupOf (closureU d.Z d.ZS) ∧
        d.V = (center (pairP d.Z d.ZS g)).map (pairP d.Z d.ZS g).subtype := by
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hf := original_conjugates_centralize hG d hM hfixed
  have hab := original_U_nonabelian hG d hempty hM hu hmany hfixed hnon
  have hh := original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon
  have hspan := original_residual_span hG d hempty hM hu hmany
  have ho := Source49.ordinary_from_original hG d hempty hM hu hmany hfixed
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have him := (source_lemma_15_3_7_of_orthogonal_action
    hG d.T hempty d.action hM hu hmany hne).1
  let := span_image_elementary d (centralizerH d.Z) h
  have hother : ¬ d.action.image (closureU d.Z d.ZS) ≤
      OrthogonalGeometry.Source50Model.planePart (d.action.sylowImage d.T d.sylow_le) := by
    have he : d.action.image d.S = OrthogonalGeometry.Source50Model.planePart
        (d.action.sylowImage d.T d.sylow_le) := by
      rw [d.action.image_planeStabilizer,OrthogonalGeometry.setwise_plane_eq_ker]
      rfl
    rw [← he]
    exact nonabelian_image_outside_stabilizer d (centralizerH d.Z) h hab
  have hmove : (OrthogonalGeometry.Source50Model.movement
      (d.action.image (closureU d.Z d.ZS))).map d.action.vectorEmbedding =
        d.V ⊓ closureU d.Z d.ZS := by
    exact (d.action.map_displacement (closureU d.Z d.ZS)
      (h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le))).trans
        (nonabelian_intersections d (centralizerH d.Z) h hf hnon hab).2.1.symm
  obtain ⟨g,hg,h26,hmark⟩ := PairGeometry.exists_g26_hypothesis_marked d h ho.1 him
    (d.V ⊓ closureU d.Z d.ZS) hh.1 hh.2 inf_le_right hspan hother hmove
  refine ⟨g,hg,h26,?_⟩
  let := moduleSectionNormal h26 h26.I_eq_LU
  let := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
  have hSyl : ∃ P : Sylow 2 d.M, (P : Subgroup d.M).map d.M.subtype = d.T :=
    ⟨d.T.subtype d.sylow_le,map_subgroupOf_eq_of_le d.sylow_le⟩
  obtain ⟨f,hcommon⟩ := PairGeometry.LayerAdapters.literalCanonicalSource
    d.action d.sylow_le hSyl hspan h26
  exact ⟨f,hcommon,hmark,PairGeometry.literal_extraspecial hh.1 inf_le_right hspan h26 rfl⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
