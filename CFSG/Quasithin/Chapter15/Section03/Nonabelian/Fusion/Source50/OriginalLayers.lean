module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalPair

/-!
# The original determinant marking on the two canonical layers

At the multiplicity-one conclusion supplied by source58, the same source54
module witness constructs both layer actions. Its marked determinant
identity passes directly to their lower coordinates; the quotient-pair
witness uses those same layers. This is the literal input consumed by the
source60 orthogonal and cubic calculations.

Source: Aschbacher–Smith, 15.3.54, 58–60, printed pp.1146,1149–1150.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open ChapterA.Section05To06 ChapterG.Section02
open OrthogonalPlusFour OrthogonalPlusFour.Chapter15Collapse
open Core.Automizers.Models Cubic.MLocal.Structure
variable {G : Type*} [Group G] [Finite G]

 theorem original_marked_layers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) (h26 : Hypothesis (Chapter15.setup d.Z
      (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g)
    [(d.V.subgroupOf (pairP d.Z d.ZS g)).Normal]
    (hIM : pairI d.Z d.ZS g ≤ d.M) :
    letI := moduleSectionNormal h26 h26.I_eq_LU
    letI := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
    ∀ f : SourceModuleData h26,
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity →
      f.decomposition.leftMultiplicity = 1 →
      (∀ v : (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T).VL,
        ClassicalOrthogonal.FourPlusMatrix.determinantForm (h26.coordinates v).toAdd =
          FusionCore.orthogonalCoordinateValue (d.action.coordinates
            ((MulEquiv.subgroupCongr (original_residual_span hG d hempty hM hu hmany)) v))) →
      ∃ layers : LayerActions (pairI d.Z d.ZS g) d.Y (pairP d.Z d.ZS g) d.V
        (pairI_normalizes_pairP d.Z d.ZS g) (hIM.trans d.action.normalizes),
        (∀ v : d.V, (layers.lowerCoordinates v).toAdd.det =
          FusionCore.orthogonalCoordinateValue (d.action.coordinates v)) ∧
        Nonempty (NaturalQuotientPair d.action (pairI d.Z d.ZS g)
          (pairP d.Z d.ZS g) hIM (pairI_normalizes_pairP d.Z d.ZS g)) := by
  let := moduleSectionNormal h26 h26.I_eq_LU
  let := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
  intro f hcommon hone hmark
  have hZS := (original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon).1
  have hspan := original_residual_span hG d hempty hM hu hmany
  let layers := PairGeometry.LayerAdapters.literalLayersOfSourceData d.action hZS inf_le_right
    hspan h26 f rfl hcommon hone hIM
  refine ⟨layers,?_,⟨PairGeometry.LayerAdapters.literalNaturalPairOfSourceData d.action
    hZS inf_le_right hspan h26 f rfl hcommon hone hIM⟩⟩
  intro v
  let w := (MulEquiv.subgroupCongr hspan).symm v
  have he := PairGeometry.LayerAdapters.literalLayersOfSourceData_determinant d.action
    hZS inf_le_right hspan h26 f rfl hcommon hone hIM w
  have hv := he.trans (hmark w)
  have hx : (MulEquiv.subgroupCongr (Chapter15.VL_eq (Zperp := d.V ⊓ closureU d.Z d.ZS)
      (T := (d.T : Subgroup G)) hspan)) w = v := by
    change (MulEquiv.subgroupCongr hspan) ((MulEquiv.subgroupCongr hspan).symm v) = v
    exact MulEquiv.apply_symm_apply _ _
  rw [hx] at hv
  simpa only [w,MulEquiv.apply_symm_apply,ClassicalOrthogonal.FourPlusMatrix.determinantForm_apply] using hv

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
