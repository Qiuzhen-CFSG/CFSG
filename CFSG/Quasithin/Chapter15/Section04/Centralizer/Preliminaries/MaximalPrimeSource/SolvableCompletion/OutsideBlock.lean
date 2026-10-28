module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SolvableCompletion.Preparation

/-!
# The literal solvable outside-block input in 15.4.3

Apply the proved solvable C.1.29 consequence inside the Fitting-preimage join.
Two-perfection puts its block in the normal Fitting preimage, so subnormality
extends to the original overgroup. Both inclusion maps are retained.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.SolvableCompletion
variable {G : Type*} [Group G] [Finite G]

private theorem intrinsic_outside_block
    (hs : Group.IsSolvable G) (hc : HasCharacteristicTwo G)
    (hqt : IsSQTK KnownSimple.IsKnownSimple G)
    (R M : Subgroup G) (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hout : ¬ (fittingSubgroup (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ M) :
    ∃ L : Subgroup G,
      L ≤ (fittingSubgroup (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ∧
      ¬ L ≤ M ∧ ChapterC.IsBlock L ∧ ChapterC.IsAlternatingBlock L 3 := by
  let : Group.IsSolvable G := hs
  let F := (fittingSubgroup (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G))
  let D := F ⊔ R
  have hFD : F ≤ D := le_sup_left
  have hRD : R ≤ D := le_sup_right
  obtain ⟨S, hS⟩ := fitting_preimage_sylow R hr
  have hSM : (S : Subgroup D) = R.subgroupOf D := by
    apply Subgroup.map_injective D.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hRD]
  have hM : M.subgroupOf D < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hout (hFD.trans (subgroupOf_eq_top.mp he)))
  have hcpu : (S : Subgroup D).characteristicNormalizerClosure ≤ M.subgroupOf D := by
    rw [hSM]
    exact characteristicNormalizerClosure_subgroupOf_le hRD hcontrol
  have hd := ChapterC.RankOne.Solvable.sectionTwoHypotheses_of_proper_subgroup
    (inferInstance : Group.IsSolvable D)
    (fitting_preimage_join_characteristicTwo R hr.isPGroup hc) (M.subgroupOf D) hM
  obtain ⟨B, hBout, hb, ha⟩ :=
    ChapterC.RankOne.Solvable.outside_alternatingThree_block_of_characteristic_control
      hd (hqt.subgroup D) S (M.subgroupOf D) hcpu hM
  let FD := F.subgroupOf D
  let : FD.Normal := inferInstance
  have hgen : FD ⊔ R.subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup hFD hRD, subgroupOf_self]
  have hquot : IsPGroup 2 (D ⧸ FD) :=
    isPGroup_quotient_of_sup_eq_top FD (R.subgroupOf D) hr.isPGroup.comap_subtype hgen
  have hBF : B ≤ FD := by
    have ht := hb.short.twoPerfect.hom_eq_one_of_isPGroup hquot
      ((QuotientGroup.mk' FD).comp B.subtype)
    intro b hbb
    exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun ht ⟨b, hbb⟩)
  let L := B.map D.subtype
  have hLF : L ≤ F := by
    rintro _ ⟨b, hb, rfl⟩
    exact hBF hb
  let e : B ≃* L := equivMapOfInjective B D.subtype D.subtype_injective
  have haL : ChapterC.IsAlternatingBlock L 3 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e ha
  have hsubF : (L.subgroupOf F).IsSubnormal := by
    have he : B.comap (inclusion hFD) = L.subgroupOf F := by
      ext x
      change (⟨(x : G), hFD x.property⟩ : D) ∈ B ↔ (x : G) ∈ B.map D.subtype
      exact (Subgroup.mem_map_iff_mem D.subtype_injective).symm
    rw [← he]
    exact hb.subnormal.comap (inclusion hFD)
  refine ⟨L, hLF, ?_, ⟨inferInstance, haL.2.1,
    Subgroup.IsSubnormal.trans hLF hsubF (inferInstance : F.Normal).isSubnormal⟩, haL⟩
  intro hLM
  exact hBout (map_le_iff_le_comap.mp hLM)

theorem outside_block_of_solvable_pushingUp
    {H R M_H : Subgroup G}
    (hsetup : Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H R M_H)
    (hs : Group.IsSolvable H) (hc : HasCharacteristicTwo H)
    (hout : ¬ twoFittingPreimage H ≤ M_H) :
    ∃ L : Subgroup G, L ≤ twoFittingPreimage H ∧ ¬ L ≤ M_H ∧
      ChapterC.IsBlock (L.subgroupOf H) ∧ ChapterC.IsAlternatingBlock L 3 := by
  have ho : ¬ (fittingSubgroup (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M_H.subgroupOf H := by
    intro he
    exact hout (map_le_iff_le_comap.mpr he)
  obtain ⟨B, hBF, houtB, hb, ha⟩ := intrinsic_outside_block hs hc hsetup.sqtk
    (R.subgroupOf H) (M_H.subgroupOf H) hsetup.radical hsetup.characteristic_control ho
  let L := B.map H.subtype
  let e : B ≃* L := equivMapOfInjective B H.subtype H.subtype_injective
  refine ⟨L, map_mono hBF, ?_, ?_,
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e ha⟩
  · exact fun hLM => houtB (map_le_iff_le_comap.mp hLM)
  · simpa only [L, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using hb

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.SolvableCompletion
