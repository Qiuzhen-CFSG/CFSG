module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalRecognitionInput
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalLayers
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Complete
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.FinalAdapter

/-!
# The source56 geometry implies the original source50 contradiction

One original source54 pair and its canonical module witness supply all
scalar and layer data. Source56 contributes its chosen paired subgroup and
fixed line. The proved recognition forces multiplicity one, and its same
natural–dual coordinates instantiate the marked partner and the terminal
transfer contradiction. No source57–61 premise remains.

Source: Aschbacher–Smith, 15.3.50–61, printed pp.1145–1151.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open ChapterA.Section05To06 ChapterG.Section02
open OrthogonalPlusFour OrthogonalPlusFour.Chapter15Collapse
open Core.ResidualGeneration
variable {G : Type*} [Group G] [Finite G]

 theorem false_of_original_source56_at_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient d.Z d.ZS)]
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) (hg : g ∈ d.Y)
    (h26 : Hypothesis (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g) :
    letI := moduleSectionNormal h26 h26.I_eq_LU
    letI := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
    ∀ (f : SourceModuleData h26),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity →
      (∀ v : (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T).VL,
        ClassicalOrthogonal.FourPlusMatrix.determinantForm (h26.coordinates v).toAdd =
          FusionCore.orthogonalCoordinateValue (d.action.coordinates
            ((MulEquiv.subgroupCongr (original_residual_span hG d hempty hM hu hmany)) v))) →
      ∀ r56 : PartnerGeometry.RecognitionFields (d.T : Subgroup G) d.Z d.ZS d.V
        f.decomposition.leftMultiplicity,
        r56.Y₁ ≤ d.Y →
        (f.decomposition.leftMultiplicity = 1 → ∀ r : RecognizedAction (d.T : Subgroup G) d.Z d.ZS d.V r56.t,
          Nonempty {p : Partner.EarlierGeometry (d.T : Subgroup G) d.Z d.ZS d.V
            r56.Y₁ r56.y r56.t // p.recognized = r}) → False := by
  let := moduleSectionNormal h26 h26.I_eq_LU
  let := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
  intro f hcommon hmark r56 hY₁ hpartner
  let := d.action.elementary
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hUnon := original_U_nonabelian hG d hempty hM hu hmany hfixed hnon
  obtain ⟨hI,hIM,hVP,hmove⟩ := original_pair_scalar_fields hG d hempty hM hu hmany hfixed
    hnon g h26
  have hVN : (d.V.subgroupOf (pairP d.Z d.ZS g)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hVP.trans inf_le_left)).mpr
      ((le_centralizer_iff.mp (hVP.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer (d.V : Set G)))
  let := hVN
  obtain ⟨v,e,hT,_,_,a,_,b⟩ := original_recognition_inputs hG d hempty hM hu hmany hfixed
    hnon g h26 f hcommon r56
  have hcomm : ⁅closureU d.Z d.ZS,d.V⁆ ≤ d.V := by
    rw [commutator_comm]
    exact (module_commutator_bounds d (centralizerH d.Z) h).2.trans inf_le_left
  have hr : f.decomposition.leftMultiplicity = 1 ∧
      Nonempty (Recognition.FusionRecognition (d.T : Subgroup G) d.Z d.ZS d.V r56.t) := by
    simpa only [hT] using Recognition.fusionRecognition_of_source e a b h.UH_le_QH
      (by rw [hT]; exact h.UH_le_QH.trans h.QH_le_T) hcomm
      (by rw [hT]; exact nonabelian_span_centralizer_index d (centralizerH d.Z) h hUnon)
      r56.t (by rw [hT]; exact r56.t_mem_T) (by rw [hT]; exact r56.t_outside)
  obtain ⟨hone,⟨r⟩⟩ := hr
  obtain ⟨layers,hdet,⟨quotientPair⟩⟩ := original_marked_layers hG d hempty hM hu hmany hfixed
    hnon g h26 hIM f hcommon hone hmark
  obtain ⟨partner,hrec⟩ := hpartner hone r.recognized
  obtain ⟨_,hcenterU,hcenterP⟩ := PairGeometry.literal_extraspecial
    (original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon).1 inf_le_right
    (original_residual_span hG d hempty hM hu hmany) h26 rfl
  exact false_of_original_recognized_geometry hG d hempty hM hu hmany hfixed hnon
    g hI hIM (hVP.trans inf_le_left) hcenterP hcenterU hg hmove layers hdet quotientPair
    r56.Y₁ r56.y r56.t hY₁ r partner hrec

 theorem false_of_original_source56
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient d.Z d.ZS)]
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) (hg : g ∈ d.Y)
    (h26 : Hypothesis (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g) :
    letI := moduleSectionNormal h26 h26.I_eq_LU
    letI := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
    ∀ (f : SourceModuleData h26),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity →
      (∀ v : (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T).VL,
        ClassicalOrthogonal.FourPlusMatrix.determinantForm (h26.coordinates v).toAdd =
          FusionCore.orthogonalCoordinateValue (d.action.coordinates
            ((MulEquiv.subgroupCongr (original_residual_span hG d hempty hM hu hmany)) v))) →
      ∀ r56 : PartnerGeometry.RecognitionFields (d.T : Subgroup G) d.Z d.ZS d.V
        f.decomposition.leftMultiplicity,
        r56.Y₁ ≤ d.Y →
        (∀ r : RecognizedAction (d.T : Subgroup G) d.Z d.ZS d.V r56.t,
          Nonempty {p : Partner.EarlierGeometry (d.T : Subgroup G) d.Z d.ZS d.V
            r56.Y₁ r56.y r56.t // p.recognized = r}) → False := by
  let := moduleSectionNormal h26 h26.I_eq_LU
  let := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
  intro f hcommon hmark r56 hY₁ hpartner
  exact false_of_original_source56_at_one hG d hempty hM hu hmany hfixed hnon
    g hg h26 f hcommon hmark r56 hY₁ (fun _ => hpartner)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
