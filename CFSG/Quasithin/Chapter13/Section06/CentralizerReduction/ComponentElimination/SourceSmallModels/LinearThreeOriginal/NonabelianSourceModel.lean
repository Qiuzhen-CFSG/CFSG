module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.CenterSourceModel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCenterCoefficients
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCoefficients
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
/-!
# Natural source models in both nonabelian binary MS cases

At critical distance four, the full double-dual cover supplies the natural
coefficient map on the entire core center. Above distance four, the genuine
earlier core factors supply that map. In each case the component two-core
centralizes the center, so the moved-center construction gives the literal
source U with a surjective actor whose kernel is exactly O₂(K).

The final theorem separates these cases using the proved even critical
distance. Its prescribed-replacement input is the actual remaining MS93
(4.4) input; it assumes no C.1.34 classification alternative.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.6) and section 7;
Aschbacher--Smith C.1.34 and 13.6.22, printed pp.136--137 and 932--933.
-/

public section
open Subgroup Representation
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open MSSourceModels BinaryMS BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {K R : Subgroup G}

omit [Finite G] in
private theorem fullCover_centerProjection_action (c : FullCoreDoubleDualCover K)
    (k : K) (x y : center (blockU K))
    (hy : (y.val : K) = k * (x.val : K) * k⁻¹) :
    (c.centerProjection y).toAdd =
      BinaryLinearThree.W (linearThreeActor c.marking k) (c.centerProjection x).toAdd := by
  let xL : c.layer := ⟨x.val,c.center_le (mem_map_of_mem _ x.property)⟩
  have he := c.action k xL
  have hh : (⟨y.val,c.center_le (mem_map_of_mem _ y.property)⟩ : c.layer) =
      ⟨k * (xL : K) * k⁻¹,c.normal.conj_mem xL xL.property k⟩ := Subtype.ext hy
  exact (congrArg (fun z : c.layer => (c.projection z).toAdd) hh).trans he

theorem natural_source_model_of_full_cover (hperfect : IsPPerfect 2 K)
    (c : FullCoreDoubleDualCover K) :
    ∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      m.actor = linearThreeActor c.marking := by
  apply natural_source_model_of_center_coefficients hperfect _ c.marking c.centerProjection
    c.centerProjection_surjective c.centerProjection_eq_one_iff (fullCover_centerProjection_action c)
  rintro _ ⟨z,hz,rfl⟩ r hr
  exact mul_inv_eq_iff_eq_mul.mp (c.core_centralizes_center r hr ⟨z,hz⟩)

theorem distanceFour_source_model {h : BinaryMS.Input κ K R} (t : InputSetup h)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hc : ¬ IsMulCommutative (commutatorCore K))
    (hb : t.geometry.b t.reduction.radical = 4) :
    ∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K := by
  obtain ⟨c⟩ := t.fullCoreDoubleDualCover_of_distance_four common hc hb
  have hp : IsPPerfect 2 K := by rw [← h.residual_eq]; exact isPPerfect_pResidual 2
  obtain ⟨m,hm⟩ := natural_source_model_of_full_cover hp c
  refine ⟨m, ?_, ?_⟩
  · rw [hm]; exact linearThreeActor_surjective c.marking
  · rw [hm]; exact linearThreeActor_kernel c.marking

theorem large_source_model {h : BinaryMS.Input κ K R} (t : InputSetup h)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    ∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K := by
  have hp : IsPPerfect 2 K := by rw [← h.residual_eq]; exact isPPerfect_pResidual 2
  obtain ⟨m,hm⟩ := natural_source_model_of_center_coefficients hp (by
    rintro _ ⟨z,hz,rfl⟩ r hr
    exact mul_inv_eq_iff_eq_mul.mp (t.large_core_centralizes_center common earlier r hr ⟨z,hz⟩))
    (h.quotientEquiv.trans common.natural.marking) (t.largeCenterProjection common earlier)
    (t.largeCenterProjection_surjective common earlier)
    (t.largeCenterProjection_eq_one_iff common earlier)
    (t.largeCenterProjection_action common earlier)
  refine ⟨m, ?_, ?_⟩
  · rw [hm]; exact linearThreeActor_surjective _
  · rw [hm]; exact linearThreeActor_kernel _

open BinaryMS.MS93.DistanceEight.PathCentrality

theorem nonabelian_source_model_of_replacement (h : BinaryMS.Input κ K R)
    (hc : ¬ IsMulCommutative (commutatorCore K))
    (replacement : ∀ (t : InputSetup h),
      CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators _ p → PrescribedReplacement _ p) :
    ∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K := by
  obtain ⟨t⟩ := exists_setup h hc
  obtain ⟨common⟩ := t.commonFacts hc
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · exact distanceFour_source_model t common hc hb
  · have heven := t.geometry.even (alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at heven
    obtain ⟨n,hn⟩ := heven
    have hlarge : 4 < t.geometry.b t.reduction.radical := by
      have := common.large_distance
      omega
    exact large_source_model t common
      (Source44.SourceEarlier.earlier common hlarge (replacement t common hlarge))
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
