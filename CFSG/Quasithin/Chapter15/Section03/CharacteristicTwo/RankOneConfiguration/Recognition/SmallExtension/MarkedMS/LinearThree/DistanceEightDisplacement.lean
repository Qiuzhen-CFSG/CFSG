module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceEightOriginalAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceFourComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceComplete
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalDisplacement

/-!
# Original fixed-factor action and the remaining binary source obstruction

Transport the intrinsic source four-group through the actual join inclusion.
Under the exact whole fixed-factor equality, its original-core displacement
is [C_Q(L),O2(LR)]. The displacement theorem makes this subgroup central in
LR. If nontrivial, it has order two and MS3 says its subgroup inside the
original R is not characteristic.

The final theorem combines the complete abelian and distance-four source
branches with the distance-eight source sections, original Sylow movement,
and radical inequality. It gives the full binary source alternatives or the
explicit central displacement line. It does not assert C.1.34: exclusion of
that second alternative remains with qt-rank-two-ms93, together with final
linearThree and D/E assembly. The only assumed earlier-source equality is
the exact local whole fixed-factor statement owned by
qt-ms93-distance-eight-fixed-factor.

Source: Aschbacher--Smith C.1.34, printed pp.136--137;
Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5) and Section 7,
printed pp.890--900, 932--933.
-/
public section
open Subgroup
open CFSG.Quasithin.ChapterC
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
local notation "msCenter" =>
  CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- With the separately owned fixed-factor equality, the original action on
C_Q(L) is trivial or has a central displacement line which is not characteristic
in the original radical. This does not assume original fixed-factor centrality. -/
theorem SmallMSPair.distance_eight_original_displacement (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hfixed : BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
      centralizer (BinaryMS.MS93.Ltilde t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) :
        Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical)) :
    let C := msQ L R ⊓ centralizer (L : Set G)
    let D := ⁅C,(L ⊔ R).pCoreIn 2⁆
    D ≤ msCenter (L ⊔ R) ∧
      (D = ⊥ ∨ (Nat.card D = 2 ∧ ¬ (D.subgroupOf R).Characteristic)) := by
  let J := L ⊔ R
  let C := msQ L R ⊓ centralizer (L : Set G)
  let D := ⁅C,J.pCoreIn 2⁆
  let D₀ := ⁅t.reducedCentralFour,pCore 2 J⁆
  have hc' : ¬ IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf J)) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L R).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv L R).symm x) ((binaryCoreEquiv L R).symm y)
  obtain ⟨common⟩ := t.commonFacts hc'
  have earlier := BinaryMS.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hCjoin : C ≤ J := inf_le_left.trans (msQ_le_join L R)
  have hCsub : msQ (L.subgroupOf J) (R.subgroupOf J) ⊓
      centralizer (L.subgroupOf J : Set J) = C.subgroupOf J := by
    rw [msQ_subgroupOf le_sup_left le_sup_right]
    ext x
    constructor
    · rintro ⟨hx,hcx⟩
      exact ⟨hx,fun l hl => congrArg Subtype.val (hcx ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)⟩
    · rintro ⟨hx,hcx⟩
      exact ⟨hx,fun l hl => Subtype.ext (hcx l hl)⟩
  have hCmap : t.reducedCentralFour.map J.subtype = C := by
    rw [← t.fixed_eq_reducedCentralFour hfixed,hCsub,map_subgroupOf_eq_of_le hCjoin]
  have hDmap : D₀.map J.subtype = D := by
    rw [map_commutator,hCmap]
    rfl
  have hDcentral : D ≤ msCenter J := by
    rw [← hDmap]
    exact map_mono (t.reducedCentralFour_core_displacement_central common earlier)
  change D ≤ msCenter J ∧ (D = ⊥ ∨ (Nat.card D = 2 ∧ ¬ (D.subgroupOf R).Characteristic))
  refine ⟨hDcentral,?_⟩
  by_cases hz : D₀ = ⊥
  · left
    rw [← hDmap,hz,Subgroup.map_bot]
  · right
    have hcard : Nat.card D = 2 := by
      rw [← hDmap,card_map_of_injective J.subtype_injective]
      exact t.reducedCentralFour_core_displacement_card common earlier hz
    refine ⟨hcard,?_⟩
    intro hchar
    have hDR : D ≤ R := by
      rw [← hDmap]
      have hle : D₀ ≤ R.subgroupOf J :=
        (commutator_le_right _ _).trans (h.binaryInput e).radical.twoCore_le
      have hm := map_mono (f := J.subtype) hle
      rwa [map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)] at hm
    have hn : ((D.subgroupOf R).map R.subtype).subgroupOf J |>.Normal := by
      rw [map_subgroupOf_eq_of_le hDR,← hDmap,subgroupOf_map_subtype_eq]
      let := t.reducedCentralFour_core_displacement_characteristic common earlier
      infer_instance
    have hzero := h.characteristic (D.subgroupOf R) hchar hn
    have hm := congrArg (map R.subtype) hzero
    rw [map_subgroupOf_eq_of_le hDR,Subgroup.map_bot] at hm
    have hc1 : Nat.card D = 1 := card_eq_one.mpr hm
    omega


/-- The complete original distance-eight alternative follows in the trivial-action
branch. Its only other branch is the explicit original central displacement line. -/
theorem SmallMSPair.distance_eight_source_or_central_displacement (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hfixed : BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
      centralizer (BinaryMS.MS93.Ltilde t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) :
        Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical))
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    (∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e') ∨
      (let D := ⁅msQ L R ⊓ centralizer (L : Set G),(L ⊔ R).pCoreIn 2⁆
       D ≤ msCenter (L ⊔ R) ∧ Nat.card D = 2 ∧ ¬ (D.subgroupOf R).Characteristic) := by
  obtain ⟨hcentral,hzero | ⟨hcard,hchar⟩⟩ :=
    h.distance_eight_original_displacement e hc t hb hfixed
  · exact Or.inl (h.distance_eight_source_of_original_core_centralizes e hc t hb hfixed
      (commutator_eq_bot_iff_le_centralizer.mp hzero) hS hRS)
  · exact Or.inr ⟨hcentral,hcard,hchar⟩

/-- All binary source branches, with the sole remaining original-action obstruction
retained as an explicit alternative. The whole fixed-factor hypothesis is exactly
qt-ms93-distance-eight-fixed-factor's local obligation; qt-rank-two-ms93 still
owns exclusion of the displayed central line and final linearThree assembly. -/
theorem SmallMSPair.binary_source_or_central_displacement (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hfixed : ∀ t : BinaryMS.MS93.InputSetup (h.binaryInput e),
      4 < t.geometry.b t.reduction.radical →
      BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
      centralizer (BinaryMS.MS93.Ltilde t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) :
        Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical))
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    (∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e') ∨
      (let D := ⁅msQ L R ⊓ centralizer (L : Set G),(L ⊔ R).pCoreIn 2⁆
       D ≤ msCenter (L ⊔ R) ∧ Nat.card D = 2 ∧ ¬ (D.subgroupOf R).Characteristic) := by
  by_cases hc : IsMulCommutative (msQ L R)
  · exact Or.inl (h.abelian_source e hc S hS hRS)
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
  · exact Or.inl (h.distance_four_source_complete e hc t hb hS hRS)
  · have hlarge : 4 < t.geometry.b t.reduction.radical := by
      have he := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
      change Even (t.geometry.b t.reduction.radical) at he
      obtain ⟨n,hn⟩ := he
      have hl := common.large_distance
      omega
    exact h.distance_eight_source_or_central_displacement e hc t hlarge
      (hfixed t hlarge) S hS hRS
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
