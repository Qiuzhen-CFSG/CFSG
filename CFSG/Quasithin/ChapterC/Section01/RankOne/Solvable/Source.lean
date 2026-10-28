module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.AmbientExtension
public import CFSG.KnownSimple.CarrierCatalogue
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The solvable outside-block consequence of C.1.29

Choose a genuine minimal parabolic outside characteristic-normalizer control.
The solvable local pushing-up theorem constructs its original A3-block. Its
Thompson commutator and module containment give subnormality of the same block
in the original group. No outside-block, GN-pair or classification conclusion
is supplied as an input.

Source: Aschbacher--Smith C.1.26--29, printed pp.132--134. The full SQTK source
domain is retained, although solvability suffices for the module calculations.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.Solvable
variable {G : Type*} [Group G] [Finite G]

theorem outside_alternatingThree_block_of_characteristic_control
    (h : Stellmacher.SectionTwo.Hypotheses G)
    (_hqt : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hM : M < ⊤) :
    ∃ K : Subgroup G, ¬ K ≤ M ∧ IsBlock K ∧ IsAlternatingBlock K 3 := by
  obtain ⟨H, hH, hout⟩ := exists_minimalParabolic_not_le h T M hcpu hM
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.le
  have hh := sectionTwoHypotheses_of_sylow_le h T H hTH
  have hP := characteristic_obstruction_of_not_le T H M hTH hcpu hout
  have hu := uniqueMaximalContaining_of_minimalParabolic T H hH
  have hMH : M.subgroupOf H < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hout (subgroupOf_eq_top.mp he))
  have hTM : (T : Subgroup G) ≤ M := by
    have hTne := T.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order)
    exact (T : Subgroup G).le_normalizer.trans ((normalizer_le_characteristicNormalizerClosure_self
      (T : Subgroup G) hTne).trans hcpu)
  obtain ⟨K₀, hKout, hb, ha, hJ, hU⟩ := exists_outside_alternatingThree_block
    hh (T.subtype hTH) hP hu (M.subgroupOf H) (comap_mono hTM) hMH
  let K := K₀.map H.subtype
  let e : K₀ ≃* K := equivMapOfInjective K₀ H.subtype H.subtype_injective
  have hKH : K ≤ H := map_subtype_le _
  have hsub : (K.subgroupOf H).IsSubnormal := by
    simpa only [K, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using
      hb.subnormal
  have haK : IsAlternatingBlock K 3 := isAlternatingBlock_of_equiv e ha
  have hJK : K = ⁅K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have hm := congrArg (Subgroup.map H.subtype) hJ
    rw [map_commutator, ← Stellmacher.elementaryAbelianMaxJ_map_injective
      H.subtype H.subtype_injective, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH] at hm
    exact hm
  have hUK : (blockU K).map K.subtype ≤
      (Stellmacher.SectionTwo.vSubgroup (T.subtype hTH)).map H.subtype := by
    rw [← blockU_map_equiv e, map_map]
    have hm := Subgroup.map_mono (f := H.subtype) hU
    rw [map_map] at hm
    exact hm
  refine ⟨K, ?_, ⟨inferInstance, haK.2.1,
    isSubnormal_of_local_alternatingThree h T hTH hKH hsub haK hJK hUK⟩, haK⟩
  intro hKM
  exact hKout ((map_le_iff_le_comap).mp hKM)

theorem solvable_C129_outside_block
    (hs : Group.IsSolvable G) (hqt : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hM : M < ⊤) :
    ∃ K : Subgroup G, ¬ K ≤ M ∧ IsBlock K ∧ IsAlternatingBlock K 3 := by
  exact outside_alternatingThree_block_of_characteristic_control
    (sectionTwoHypotheses_of_proper_subgroup hs
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf) M hM)
    hqt T M hcpu hM

end CFSG.Quasithin.ChapterC.RankOne.Solvable
