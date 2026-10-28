module

public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Stellmacher.SectionTwo.LemmaTwoOne
public import Stellmacher.UniqueMaximalContainingMap
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Mathlib.Order.LatticeIntervals

/-!
# Selecting the solvable minimal parabolic outside characteristic control

The normalizer-plus-parabolics generation theorem selects an actual minimal
parabolic outside the prescribed proper subgroup. Characteristic-normalizer
control restricts to it and supplies the original characteristic-Sylow
obstruction. All Sylow and subgroup maps remain the inclusions.

Source: Aschbacher--Smith C.1.26--29, printed pp.132--134.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.Solvable
variable {G : Type*} [Group G] [Finite G]

theorem sectionTwoHypotheses_of_proper_subgroup
    (hs : Group.IsSolvable G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (M : Subgroup G) (hM : M < ⊤) : Stellmacher.SectionTwo.Hypotheses G := by
  refine ⟨hs, ?_, hc⟩
  have hQ : pCore 2 G ≠ ⊥ := by
    intro he
    have ht : (⊤ : Subgroup G) ≤ (⊥ : Subgroup G) := by
      rw [he] at hc
      intro x _
      apply hc
      intro y hy
      have hy1 : y = 1 := hy
      rw [hy1, mul_one, one_mul]
    exact hM.not_ge (ht.trans bot_le)
  let : Nontrivial (pCore 2 G) := (nontrivial_iff_ne_bot _).mpr hQ
  obtain ⟨n, hn, hcard⟩ := (pCore_isPGroup (p := 2) (G := G)).nontrivial_iff_card.mp
    (inferInstance : Nontrivial (pCore 2 G))
  apply even_iff_two_dvd.mpr
  apply dvd_trans _ (card_subgroup_dvd_card (pCore 2 G))
  rw [hcard]
  exact dvd_pow_self 2 (Nat.ne_of_gt hn)

theorem exists_minimalParabolic_not_le
    (h : Stellmacher.SectionTwo.Hypotheses G) (T : Sylow 2 G)
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hM : M < ⊤) :
    ∃ H : Subgroup G, ChapterB.IsMinimalParabolicOver T H ∧ ¬ H ≤ M := by
  have hT : (T : Subgroup G) ≠ ⊥ :=
    T.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order)
  have hNM := (normalizer_le_characteristicNormalizerClosure_self
    (T : Subgroup G) hT).trans hcpu
  by_contra! hn
  have hh := sup_le (sSup_le hn) hNM
  change sSup {P | ChapterB.IsMinimalParabolicOver T P} ⊔
    normalizer (T : Set G) ≤ M at hh
  rw [ChapterB.minimalParabolics_sup_normalizer T] at hh
  exact hM.not_ge hh

theorem sectionTwoHypotheses_of_sylow_le
    (h : Stellmacher.SectionTwo.Hypotheses G) (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    Stellmacher.SectionTwo.Hypotheses H := by
  let : Group.IsSolvable G := h.solvable
  refine ⟨inferInstance, ?_, centralizer_pCore_le_of_pCore_le H
    h.centralizer_twoCore_le ((pCore_isPGroup.le_sylow_of_normal T).trans hTH)⟩
  have hT : (T : Subgroup G) ≠ ⊥ :=
    T.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order)
  have hS : ((T.subtype hTH : Sylow 2 H) : Subgroup H) ≠ ⊥ := by
    intro he
    apply hT
    have hm := congrArg (Subgroup.map H.subtype) he
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH, Subgroup.map_bot] using hm
  let : Nontrivial (T.subtype hTH : Sylow 2 H) := (nontrivial_iff_ne_bot _).mpr hS
  obtain ⟨n, hn, hc⟩ := (T.subtype hTH).isPGroup'.nontrivial_iff_card.mp
    (inferInstance : Nontrivial (T.subtype hTH : Sylow 2 H))
  apply even_iff_two_dvd.mpr
  apply dvd_trans _ (card_subgroup_dvd_card (T.subtype hTH : Subgroup H))
  rw [hc]
  exact dvd_pow_self 2 (Nat.ne_of_gt hn)

omit [Finite G] in
theorem uniqueMaximalContaining_of_minimalParabolic
    (T : Sylow 2 G) (H : Subgroup G)
    (hH : ChapterB.IsMinimalParabolicOver T H) :
    Stellmacher.IsUniqueMaximalContaining
      (T.subtype hH.1.1.le : Subgroup H) ⊤ := by
  obtain ⟨M, hM, hu⟩ := hH.1.2
  have hMH : M ≤ H := hM.2.le
  let e : Subgroup H ≃o Set.Iic H := Subgroup.MapSubtype.orderIso H
  have hco (N : Subgroup H) : IsCoatom N ↔ N.map H.subtype ⋖ H := by
    have hm : ((e N : Set.Iic H) : Subgroup G) = N.map H.subtype := rfl
    simpa only [Set.Iic.isCoatom_iff, hm] using (e.isCoatom_iff N).symm
  apply (Stellmacher.uniqueMaximalContaining_top_iff _).mpr
  refine ⟨M.subgroupOf H, ?_, comap_mono hM.1, ?_⟩
  · apply (hco _).mpr
    simpa only [map_subgroupOf_eq_of_le hMH] using hM.2
  · intro N hN hTN
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hMH]
    apply hu
    refine ⟨?_, (hco N).mp hN⟩
    have hm := Subgroup.map_mono (f := H.subtype) hTN
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hH.1.1.le] using hm

omit [Finite G] in
theorem characteristic_obstruction_of_not_le
    (T : Sylow 2 G) (H M : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hout : ¬ H ≤ M) :
    ∀ K : Subgroup (T.subtype hTH), K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T.subtype hTH : Subgroup H).subtype).Normal := by
  have hc := characteristicNormalizerClosure_subgroupOf_le hTH hcpu
  have hm : M.subgroupOf H < ⊤ := lt_top_iff_ne_top.mpr (fun he =>
    hout (subgroupOf_eq_top.mp he))
  intro K hK hne
  let : K.Characteristic := hK
  exact not_normal_of_characteristicNormalizerClosure_le
    (T.subtype hTH : Subgroup H) (M.subgroupOf H) hm hc K hne

end CFSG.Quasithin.ChapterC.RankOne.Solvable
