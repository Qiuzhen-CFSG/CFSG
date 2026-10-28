module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Source56Consumer
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Complete

/-!
# The original abelian span at the involution centralizer

A nonabelian span forces the marked G.2.6 pair and its source56 partner
geometry. The actual recognition then has multiplicity one, and the marked
partner gives the terminal transfer contradiction. Every source51–61 input
is constructed from the original local hypotheses and the earlier fixed-plane
centralizer bound. The conclusion is the Mc-span used by the E endgame.

Source: Aschbacher–Smith, 15.3.50, printed pp.1145–1151.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open ChapterA.Section05To06 ChapterG.Section02
open OrthogonalPlusFour OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G] [Finite G]

theorem local_span_abelian_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M) :
    IsMulCommutative (conjugateSpanBy d.V d.Mc) := by
  have hMc := FusionCore.CosetSetup.OriginalSource.source_partner_eq hG d hempty hM hu hmany
  rw [hMc]
  change IsMulCommutative (localSpan d.V (centralizerH d.Z))
  by_contra hnon
  obtain ⟨g,hg,h26,hsource⟩ := original_pair_exists hG d hempty hM hu hmany hfixed hnon
  let := moduleSectionNormal h26 h26.I_eq_LU
  let := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
  obtain ⟨f,hcommon,hmark,_,_,_⟩ := hsource
  let := original_vector_normal hG d hempty hM hu hmany hfixed
  let := original_vector_elementary hG d hempty hM hu hmany hfixed hnon g h26
  obtain ⟨r56,hY₁,hpartner⟩ := PartnerGeometry.source56_inputs
    hG d hempty hM hu hmany hfixed hnon g h26 f hcommon hmark
  exact false_of_original_source56_at_one hG d hempty hM hu hmany hfixed hnon
    g hg h26 f hcommon hmark r56 hY₁ hpartner

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
