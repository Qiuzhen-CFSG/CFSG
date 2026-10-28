module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceEightSourceSections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightMovement

/-!
# The original radical inequality in the distance-eight alternative

The source edge calculation supplies a component element centralizing the
original Sylow centralizer and moving the characteristic replacement. If R
were the two-core of C_{L join R}(Omega_1 Z(S)), this element would normalize
R, hence its characteristic replacement. This contradiction proves the
literal inequality of C.1.34(4), with no additional movement premise.

The final consumer retains the common marking of all four sections. The
whole fixed-factor equality remains with qt-ms93-distance-eight-fixed-factor;
original fixed-factor centrality and final classification assembly remain
with qt-rank-two-ms93. Neither premise is inferred from replacement centrality.
Source: Aschbacher--Smith C.1.34(4), printed pp.136--137; the final remark
on MS93 cases (11)--(13), printed p.831.
-/
public section
open Subgroup
open CFSG.Quasithin.ChapterC
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R S : Subgroup G}

/-- The distance-eight radical inequality uses the original Sylow and radical,
and requires neither the whole fixed-factor equality nor its original centrality. -/
theorem SmallMSPair.distance_eight_not_centralizer_core (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    MSNotCentralizerCore L R S := by
  let J := L ⊔ R
  obtain ⟨P,hP⟩ := hS
  have hSP : S.subgroupOf J = (P : Subgroup J) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hRP : R.subgroupOf J ≤ (P : Subgroup J) := hSP ▸ comap_mono hRS
  have hSJ : S ≤ J := hP ▸ map_subtype_le (P : Subgroup J)
  intro heq
  apply t.distance_eight_replacement_movement common hb P hRP
  intro l hl
  have hlC : (l : G) ∈ centralizer (omegaCenterIn S : Set G) := by
    intro z hz
    have hzS : z ∈ S := map_subtype_le _ hz
    have hzC : z ∈ centralizer (S : Set G) := by
      obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩ := hz
      intro s hs
      exact congrArg S.subtype (mem_center_iff.mp b.property ⟨s,hs⟩)
    let zJ : J := ⟨z,hSJ hzS⟩
    have hzP : zJ ∈ centralizer (P : Set J) := by
      intro p hp
      exact Subtype.ext (hzC p (hP ▸ mem_map_of_mem J.subtype hp))
    exact congrArg Subtype.val (hl.2 zJ hzP)
  let C := J ⊓ centralizer (omegaCenterIn S : Set G)
  have hlN : (l : G) ∈ normalizer (R : Set G) := by
    have hn : (l : G) ∈ normalizer (C.pCoreIn 2 : Set G) :=
      normalizer_le_normalizer_characteristic_image C (pCore 2 C)
        (C.le_normalizer ⟨l.property,hlC⟩)
    exact (congrArg (fun D : Subgroup G => (l : G) ∈ normalizer (D : Set G)) heq).mpr hn
  have hjN : l ∈ normalizer (R.subgroupOf J : Set J) :=
    (Subgroup.le_normalizer_comap J.subtype) hlN
  let := t.reduction.characteristic
  exact normalizer_le_normalizer_characteristic_image (R.subgroupOf J)
    t.reduction.subgroup hjN

/-- Apply the proved radical inequality to the complete same-marking section
assembly. Only the fixed-factor equality and original fixed-factor centrality
remain; both retain their existing owners. -/
theorem SmallMSPair.distance_eight_source_of_original_core_centralizes
    (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hfixed : BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
      centralizer (BinaryMS.MS93.Ltilde t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) :
        Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical))
    (hcore : msQ L R ⊓ centralizer (L : Set G) ≤
      centralizer ((L ⊔ R).pCoreIn 2 : Set G))
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  have hc' : ¬ IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L R).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv L R).symm x) ((binaryCoreEquiv L R).symm y)
  obtain ⟨common⟩ := t.commonFacts hc'
  exact h.distance_eight_source_of_core_centralizes e hc t hb hfixed hcore S
    (h.distance_eight_not_centralizer_core e t common hb hS hRS)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
