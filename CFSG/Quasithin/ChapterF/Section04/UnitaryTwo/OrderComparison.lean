module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.SourceClasses
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.EndpointFusion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.CommonCover
public import Theory.GroupTheory.InvolutionClassOrderComparison
/-!
# Thompson order comparison for the ordinary U₄(2) completion

The two complete involution classes, their centralizer equivalences and
marked fusion comparisons identify the Thompson fibers and force order 25,920.
The result is the literal F.4.43 consumer.
-/

open Subgroup
open Theory.GroupTheory.CentralizerSmallKernelTransport
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourShortRoot
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.OrderComparison
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour ShortRootQuotient ShortRootFusion ShortRootCentralizer ModelClasses SourceClasses EndpointFusion
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "P" => pointParabolic 1 hn
local notation "R" => planeParabolic 1 hn
local notation "M" => ProjectiveGroup 1 hn
local notation "X" => shortCentralizer F σ hσ
local notation "mc" => CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.modelCompletion
local notation "mi" => MonoidHom.id M
local notation "zM" => longPoint.val
local notation "tM" => sourceShort mc mi

variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

omit [Finite G] in
def longCentralizerEmbedding : P →* centralizer ({(i (c.left longPoint))} : Set G) :=
  (i.comp c.left).codRestrict _ (fun p => mem_centralizer_singleton_iff.mpr (by
    have h := congrArg (i.comp c.left)
      (mem_center_iff.mp (PointCore.rootSubgroup_central longPoint_mem_root) p)
    simpa only [map_mul,MonoidHom.comp_apply] using h))

omit [Finite G] in
theorem longCentralizerEmbedding_injective (hi : Function.Injective i) :
    Function.Injective (longCentralizerEmbedding c i) := by
  intro a b he
  exact c.left_injective (hi (congrArg Subtype.val he))

omit [Finite G] in
def longCentralizerEquiv (hi : Function.Injective i)
    (hc : centralizer ({(i (c.left longPoint))} : Set G) ≤ (i.comp c.left).range) :
    P ≃* centralizer ({(i (c.left longPoint))} : Set G) :=
  MulEquiv.ofBijective (longCentralizerEmbedding c i)
    ⟨longCentralizerEmbedding_injective c i hi,by
      intro x
      obtain ⟨p,hp⟩ := hc x.property
      exact ⟨p,Subtype.ext hp⟩⟩

theorem model_centralizer_bound : centralizer ({mi ((mc).left longPoint)} : Set M) ≤ ((mi).comp (mc).left).range := by
  change centralizer ({zM} : Set M) ≤ (P).subtype.range
  rw [range_subtype,model_long_centralizer]

theorem model_normalizer : normalizer (PlainFusion.sourcePlaneRootImage mc mi : Set M) =
    ((mi).comp (mc).right).range := by
  rw [PlainFusion.sourcePlaneRootImage_eq]
  change normalizer (InvolutionPlacement.planeCore : Set M) = (R).subtype.range
  rw [range_subtype]
  exact ModelFusion.planeCore_normalizer


def longComparison (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range) : centralizer ({zM} : Set M) ≃* centralizer ({(i (c.left longPoint))} : Set G) :=
  (longCentralizerEquiv mc mi Function.injective_id model_centralizer_bound).symm.trans
    (longCentralizerEquiv c i hi hc)

def shortComparison (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) : centralizer ({tM} : Set M) ≃* centralizer ({(sourceShort c i)} : Set G) :=
  (sourceShortCentralizerEquiv mc mi Function.injective_id longPoint longPoint_order longPoint_mem_root
    model_centralizer_bound model_normalizer).symm.trans
  (sourceShortCentralizerEquiv c i hi longPoint longPoint_order longPoint_mem_root hc hnorm)

omit [Finite G] in
theorem longComparison_mark (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range) :
    longComparison c i hi hc (Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint zM) =
      Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint (i (c.left longPoint)) := by
  have he : longCentralizerEquiv mc mi Function.injective_id model_centralizer_bound longPoint =
      Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint zM := by
    apply Subtype.ext
    exact (Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint_coe zM).symm
  change longCentralizerEquiv c i hi hc
    ((longCentralizerEquiv mc mi Function.injective_id model_centralizer_bound).symm _) = _
  rw [← he,MulEquiv.symm_apply_apply]
  apply Subtype.ext
  exact (Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint_coe _).symm

theorem shortComparison_mark (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    shortComparison c i hi hc hnorm (Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint tM) =
      Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint (sourceShort c i) := by
  have hm : Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint tM = ambientMark mc mi := by
    apply Subtype.ext
    exact Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint_coe _
  have hg : Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint (sourceShort c i) = ambientMark c i := by
    apply Subtype.ext
    exact Theory.GroupTheory.InvolutionClassOrderComparison.centralizerPoint_coe _
  rw [hm,hg]
  change sourceShortCentralizerEquiv c i hi longPoint longPoint_order longPoint_mem_root hc hnorm
    ((sourceShortCentralizerEquiv mc mi Function.injective_id longPoint longPoint_order longPoint_mem_root
      model_centralizer_bound model_normalizer).symm (ambientMark mc mi)) = ambientMark c i
  rw [← sourceShortCentralizerEquiv_mark mc mi Function.injective_id longPoint longPoint_order longPoint_mem_root
    model_centralizer_bound model_normalizer, MulEquiv.symm_apply_apply]
  exact sourceShortCentralizerEquiv_mark c i hi longPoint longPoint_order longPoint_mem_root hc hnorm

theorem longComparison_long_fusion (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) (a : centralizer ({zM} : Set M)) :
    IsConj zM a.val ↔ IsConj (i (c.left longPoint)) (longComparison c i hi hc a).val := by
  let eM := longCentralizerEquiv mc mi Function.injective_id model_centralizer_bound
  let p := eM.symm a
  have he : p.val = a.val := congrArg Subtype.val (eM.apply_symm_apply a)
  change IsConj zM a.val ↔ IsConj (i (c.left longPoint)) (i (c.left p))
  rw [← he]
  exact point_involution_class_iff c i hi longPoint longPoint_order longPoint_mem_root hc hnorm
    longPoint p (by simpa only [longPoint_order] using pow_orderOf_eq_one longPoint)

theorem shortPoint_sq : shortPoint ^ 2 = 1 := by
  apply Subtype.ext
  have h := pow_orderOf_eq_one (sourceShort mc mi)
  rw [sourceShort_order mc mi Function.injective_id] at h
  have he : sourceShort mc mi = shortPoint.val := short_image mc mi
  change shortPoint.val ^ 2 = 1
  exact he ▸ h

theorem longComparison_short_fusion (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) (a : centralizer ({zM} : Set M)) :
    IsConj tM a.val ↔ IsConj (sourceShort c i) (longComparison c i hi hc a).val := by
  let eM := longCentralizerEquiv mc mi Function.injective_id model_centralizer_bound
  let p := eM.symm a
  have he : p.val = a.val := congrArg Subtype.val (eM.apply_symm_apply a)
  have hm : tM = shortPoint.val := short_image mc mi
  have hg : (sourceShort c i) = i (c.left shortPoint) := short_image c i
  change IsConj tM a.val ↔ IsConj (sourceShort c i) (i (c.left p))
  rw [← he,hm,hg]
  exact point_involution_class_iff c i hi longPoint longPoint_order longPoint_mem_root hc hnorm
    shortPoint p shortPoint_sq

theorem right_long_sq : longRight ^ 2 = 1 := by
  apply Subtype.ext
  change longPoint.val ^ 2 = 1
  exact congrArg (fun p : P => p.val)
    (show longPoint ^ 2 = 1 from by simpa only [longPoint_order] using pow_orderOf_eq_one longPoint)

theorem right_short_sq : shortRight ^ 2 = 1 := by
  apply Subtype.ext
  have hm : shortRight.val = shortPoint.val := short_image mc mi
  change shortRight.val ^ 2 = 1
  rw [hm]
  exact congrArg (fun p : P => p.val) shortPoint_sq

theorem shortComparison_long_fusion (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) (a : centralizer ({tM} : Set M)) :
    IsConj zM a.val ↔ IsConj (i (c.left longPoint)) (shortComparison c i hi hc hnorm a).val := by
  let eM := sourceShortCentralizerEquiv mc mi Function.injective_id longPoint longPoint_order
    longPoint_mem_root model_centralizer_bound model_normalizer
  let p := eM.symm a
  have he : (matrixPlaneEquiv p.val).val = a.val := congrArg Subtype.val (eM.apply_symm_apply a)
  change IsConj zM a.val ↔ IsConj (i (c.left longPoint)) (i (c.right (matrixPlaneEquiv p.val)))
  rw [← he]
  have hz : i (c.right longRight) = (i (c.left longPoint)) := long_image c i
  rw [← hz]
  exact plane_involution_class_iff c i hi longPoint longPoint_order longPoint_mem_root hc hnorm
    longRight (matrixPlaneEquiv p.val) right_long_sq

theorem shortComparison_short_fusion (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) (a : centralizer ({tM} : Set M)) :
    IsConj tM a.val ↔ IsConj (sourceShort c i) (shortComparison c i hi hc hnorm a).val := by
  let eM := sourceShortCentralizerEquiv mc mi Function.injective_id longPoint longPoint_order
    longPoint_mem_root model_centralizer_bound model_normalizer
  let p := eM.symm a
  have he : (matrixPlaneEquiv p.val).val = a.val := congrArg Subtype.val (eM.apply_symm_apply a)
  change IsConj tM a.val ↔ IsConj (sourceShort c i) (i (c.right (matrixPlaneEquiv p.val)))
  rw [← he]
  exact plane_involution_class_iff c i hi longPoint longPoint_order longPoint_mem_root hc hnorm
    shortRight (matrixPlaneEquiv p.val) right_short_sq

/-- Original F.4.43 in the ordinary U₄(2) branch. The two complete class
catalogues and marked centralizer comparisons identify Thompson's fibers. -/
theorem source_order_long (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) : Nat.card G = 25920 := by
  let z := (i (c.left longPoint))
  let t := (sourceShort c i)
  have hzM : orderOf zM = 2 := (Subgroup.orderOf_coe longPoint).trans longPoint_order
  have htM : orderOf tM = 2 := sourceShort_order mc mi Function.injective_id
  have hzG : orderOf z = 2 :=
    (orderOf_injective (i.comp c.left) (hi.comp c.left_injective) longPoint).trans longPoint_order
  have htG : orderOf t = 2 := sourceShort_order c i hi
  have hnM : ¬ IsConj zM tM := source_long_short_nonconjugate mc mi Function.injective_id
    longPoint longPoint_order longPoint_mem_root model_centralizer_bound model_normalizer
  have hnG : ¬ IsConj z t := source_long_short_nonconjugate c i hi
    longPoint longPoint_order longPoint_mem_root hc hnorm
  have hclassesM : ∀ a : M, orderOf a = 2 → IsConj zM a ∨ IsConj tM a :=
    source_involution_classes mc mi Function.injective_id longPoint longPoint_order longPoint_mem_root
      model_centralizer_bound
  have hclassesG : ∀ a : G, orderOf a = 2 → IsConj z a ∨ IsConj t a :=
    source_involution_classes c i hi longPoint longPoint_order longPoint_mem_root hc
  have hzcount := Theory.GroupTheory.InvolutionClassOrderComparison.kappa_eq
    zM tM zM z t z hzM htM hnM hzG htG hnG
    (longComparison c i hi hc) (longComparison_mark c i hi hc)
    (longComparison_long_fusion c i hi hc hnorm) (longComparison_short_fusion c i hi hc hnorm)
  have htcount := Theory.GroupTheory.InvolutionClassOrderComparison.kappa_eq
    zM tM tM z t t hzM htM hnM hzG htG hnG
    (shortComparison c i hi hc hnorm) (shortComparison_mark c i hi hc hnorm)
    (shortComparison_long_fusion c i hi hc hnorm) (shortComparison_short_fusion c i hi hc hnorm)
  have hzcard := Nat.card_congr (longComparison c i hi hc).toEquiv
  have htcard := Nat.card_congr (shortComparison c i hi hc hnorm).toEquiv
  have hm := Theory.GroupTheory.TwoInvolutionClassOrder.card_eq zM tM hzM htM hnM hclassesM
  have hg := Theory.GroupTheory.TwoInvolutionClassOrder.card_eq z t hzG htG hnG hclassesG
  rw [hzcount,htcount,hzcard,htcard] at hm
  exact (hg.trans hm.symm).trans BinaryCompletion.projective_card

/-- The order comparison with the original arbitrary central-root marking. -/
theorem source_order (hi : Function.Injective i)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    Nat.card G = 25920 := by
  have he := root_eq_longPoint z hz hzroot
  subst z
  exact source_order_long c i hi hc hnorm

end CFSG.Quasithin.ChapterF.UnitaryTwo.OrderComparison