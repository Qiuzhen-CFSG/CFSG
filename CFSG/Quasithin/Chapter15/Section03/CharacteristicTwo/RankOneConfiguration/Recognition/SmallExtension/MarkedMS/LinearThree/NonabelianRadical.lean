module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceFourComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceEightOriginalAction

/-!
# The original radical inequality for every nonabelian binary MS core

Construct the source setup from the original nonabelian core. Its critical
distance is even and greater than two, so the complete distance-four or
distance-eight movement argument applies. The conclusion concerns the literal
original Sylow and radical and has no source-action or fixed-factor premise.

This discharges the common radical clause of C.1.34(3)--(4). The remaining
fixed-factor equality and original centrality in case (4) retain their owners;
this theorem does not assert the full module classification.
Source: Aschbacher--Smith C.1.34, printed pp.136--137; MS93 Section 7,
printed pp.932--933 and the final Main Theorem remark, printed p.831.
-/
public section
open Subgroup
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R S : Subgroup G}

/-- The original noncentralizer clause in both nonabelian alternatives of
C.1.34, with all setup, distance, movement and action premises discharged. -/
theorem SmallMSPair.nonabelian_not_centralizer_core (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    MSNotCentralizerCore L R S := by
  have hc' : ¬ IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L R).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv L R).symm x) ((binaryCoreEquiv L R).symm y)
  obtain ⟨t⟩ := BinaryMS.MS93.exists_setup (h.binaryInput e) hc'
  obtain ⟨common⟩ := t.commonFacts hc'
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · exact h.distance_four_not_centralizer_core e t common hb hS hRS
  · apply h.distance_eight_not_centralizer_core e t common _ hS hRS
    have he := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at he
    obtain ⟨n,hn⟩ := he
    have hl := common.large_distance
    omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
