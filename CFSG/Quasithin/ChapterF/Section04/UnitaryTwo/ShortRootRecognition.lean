module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ShortRootFusion
public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSmallNormalizer

/-!
# I.8.5 on the original binary short-root centralizer quotient

The marked long root's unique fixed coset descends through the actual
central short-root line. Every nonzero vector of V* is conjugate to this
root, so the whole four-group satisfies I.8.5. Its normal closure is A₅ by
the complete order-48 Bender recognition. Properness follows from the
original contrary assumption C_G(t) is not contained in the plane endpoint.

This is the recognition step of Aschbacher–Smith F.4.42, printed p.295.
No unique-fixed, Bender-model, or odd-cover premise remains. Lifting A₅
through the central line and its centralizing four-group is the next step.
-/

open Subgroup
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootRecognition
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour ShortRootQuotient ShortRootFusion
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

omit [Finite G] in
theorem ambientLine_le_endpoint : ambientLine c i ≤ (shortCentralizerEmbedding c i).range := by
  apply zpowers_le.mpr
  exact ⟨ShortRoot.mark,shortCentralizerEmbedding_mark c i⟩

omit [Finite G] in
theorem endpoint_quotient_image :
    (shortCentralizerEmbedding c i).range.map (QuotientGroup.mk' (ambientLine c i)) =
      quotientEndpoint c i := by
  rw [← MonoidHom.range_comp]
  rfl

/-- Every nonidentity vector of the original V* has a unique fixed coset. -/
theorem source_four_unique_fixed
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (v : ambientShortCentralizer c i ⧸ ambientLine c i)
    (hv : v ∈ sourceFour c i) (hv1 : v ≠ 1) :
    ∃! q : (ambientShortCentralizer c i ⧸ ambientLine c i) ⧸ quotientEndpoint c i,
      v • q = q := by
  let q := QuotientGroup.mk' (ambientLine c i)
  have hk : q.ker ≤ (shortCentralizerEmbedding c i).range := by
    rw [QuotientGroup.ker_mk']
    exact ambientLine_le_endpoint c i
  have h := UniqueFixedCoset.unique_map_of_surjective q (QuotientGroup.mk'_surjective _)
    hk (show ambientLong c i ∈ (shortCentralizerEmbedding c i).range from ⟨_,rfl⟩)
    (source_long_unique_fixed c i hi hc hnorm)
  rw [endpoint_quotient_image] at h
  exact UniqueFixedCoset.unique_of_isConj h (sourceFour_fusion c i hv hv1)

omit [Finite G] in
/-- Properness survives the original central quotient. -/
theorem quotientEndpoint_ne_top
    (hnot : ¬ ambientShortCentralizer c i ≤ (i.comp c.right).range) :
    quotientEndpoint c i ≠ ⊤ := by
  intro htop
  apply hnot
  intro g hg
  let h : ambientShortCentralizer c i := ⟨g,hg⟩
  have hmem : QuotientGroup.mk' (ambientLine c i) h ∈ quotientEndpoint c i := htop ▸ mem_top _
  obtain ⟨x,hx⟩ := hmem
  have hdiff : (shortCentralizerEmbedding c i x)⁻¹ * h ∈ ambientLine c i := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (ambientLine c i) ((shortCentralizerEmbedding c i x)⁻¹ * h) = 1
    rw [map_mul,map_inv]
    change (sourceQuotientMap c i x)⁻¹ * QuotientGroup.mk' (ambientLine c i) h = 1
    rw [hx,inv_mul_cancel]
  have hh : h ∈ (shortCentralizerEmbedding c i).range := by
    simpa only [mul_inv_cancel_left] using (shortCentralizerEmbedding c i).range.mul_mem
      (show shortCentralizerEmbedding c i x ∈ (shortCentralizerEmbedding c i).range from ⟨x,rfl⟩)
      (ambientLine_le_endpoint c i hdiff)
  obtain ⟨a,ha⟩ := hh
  refine ⟨matrixPlaneEquiv a.val,?_⟩
  exact (matrixPlaneEquiv_image c i a.val).trans (congrArg Subtype.val ha)

/-- Original I.8.5 recognition on the actual quotient in the contrary
short-centralizer case of F.4.42. No unique-fixed or model-classification
premise remains in this application. -/
theorem source_quotient_normalClosure_alternating_five
    (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (hnot : ¬ ambientShortCentralizer c i ≤ (i.comp c.right).range) :
    Nonempty (normalClosure (sourceFour c i : Set (ambientShortCentralizer c i ⧸ ambientLine c i)) ≃*
      alternatingGroup (Fin 5)) := by
  have he := root_eq_longPoint z hz hzroot
  rw [he] at hc
  exact CFSG.Quasithin.ChapterI.Section06To08.normalClosure_alternating_five_of_card_fortyEight
    (sourceFour c i) (quotientEndpoint c i) (sourceFour_le_endpoint c i)
    (sourceFour_card c i hi) (quotientEndpoint_card c i hi)
    (quotientEndpoint_ne_top c i hnot) (source_four_unique_fixed c i hi hc hnorm)
end CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootRecognition
