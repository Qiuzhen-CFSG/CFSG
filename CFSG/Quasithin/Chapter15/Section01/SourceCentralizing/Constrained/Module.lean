module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Input
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Seed
public import Theory.GroupTheory.SylowFixedSpanReduced
public import Theory.GroupTheory.ReducedNormal.Defs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
/-!
# Reducedness of the original constrained module

The span U=<Z2^L> lies in the actual C.2.7 star module and in Q1. Its seed is
fixed by S. The Sylow-fixed-span criterion proves reducedness for both LS and
LQ1, retaining the literal subgroups and their centralizer quotients.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
theorem G1_normalizes_L (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)] (hf : Facts (d.L ⧸ pCore 2 d.L)) :
    d.G1 ≤ normalizer (d.L : Set G) := by
  have hLc := (d.source_cubic_component hG h hf).1
  have hh := d.G1.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image d.G1 (primeToResidual 3 d.G1))
  rwa [←hLc] at hh

theorem U_le_starV (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    d.U t ≤ (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype := by
  apply conjugateSpanBy_le ((d.Z2_le_omega_Q1 s hM hu h t ht).trans
    (d.omega_Q1_le_starV hG h hi hf))
  have hn := (starV d.L d.Q1).le_normalizer_map (d.L ⊔ d.Q1 : Subgroup G).subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hn
  exact le_sup_left.trans hn

theorem Q1_le_S (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    d.Q1 ≤ d.S := by
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSM : d.S ≤ d.MZ := le_inf d.S_le_G1 (d.S_le_T.trans hTMc)
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict hSM inf_le_left
  have hh := map_mono (f := d.MZ.subtype) (pCore_isPGroup.le_sylow_of_normal P)
  rwa [hP] at hh

theorem U_le_Q1 (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) : d.U t ≤ d.Q1 := by
  let := hi.quasisimple
  let : (d.L.subgroupOf d.G1).Normal :=
    normal_subgroupOf_of_le_normalizer (d.G1_normalizes_L hG h hf)
  exact (d.U_le_starV s hG hM hu h hi hf t ht).trans
    ((map_mono (show starV d.L d.Q1 ≤ pCore 2 (d.L ⊔ d.Q1 : Subgroup G) from
      map_subtype_le _)).trans (source_joinCore_le_radical hi))

theorem U_elementary (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) : IsElementaryAbelian 2 (d.U t) := by
  let : IsElementaryAbelian 2 ((starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype) :=
    IsElementaryAbelian.map _
  exact IsElementaryAbelian.of_le (d.U_le_starV s hG hM hu h hi hf t ht)

theorem U_reduced (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    IsPReduced 2 ((d.U t).subgroupOf (d.L ⊔ d.S)) := by
  let := hi.quasisimple
  let := d.U_elementary s hG hM hu h hi hf t ht
  let D := d.L ⊔ d.S
  have hUS : d.U t ≤ d.S := (d.U_le_Q1 s hG hM hu h hi hf t ht).trans (d.Q1_le_S s hu)
  have hUD : d.U t ≤ D := hUS.trans le_sup_right
  have hZD : d.Z2 t ≤ D := (le_conjugateSpanBy _ _).trans hUD
  have hZS := d.Z2_le_centralizer_S s t ht
  have hSnL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans (d.G1_normalizes_L hG h hf)
  have hspan : conjugateSpanBy (d.Z2 t) D = d.U t :=
    conjugateSpanBy_sup_of_normalizes_seed _ _ _
      ((le_centralizer_iff.mp hZS).trans (Subgroup.centralizer_le_normalizer _)) hSnL
  have hDn : D ≤ normalizer (d.U t : Set G) := by
    rw [←hspan]
    exact le_normalizer_conjugateSpanBy _ _
  let U0 := (d.U t).subgroupOf D
  let Z0 := (d.Z2 t).subgroupOf D
  let : U0.Normal := normal_subgroupOf_of_le_normalizer hDn
  let : IsElementaryAbelian 2 U0 := IsElementaryAbelian.subgroupOf hUD
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict (show d.S ≤ D from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  refine ⟨inferInstance,inferInstance,
    centralizer_quotient_pCore_eq_bot_of_sylow_fixed_span U0 Z0 P
      (comap_mono (le_conjugateSpanBy _ _)) ?_ ?_⟩
  · intro z hz p hp
    exact Subtype.ext (hZS hz p (hP ▸ mem_map_of_mem D.subtype hp))
  · apply (map_le_map_iff_of_injective D.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hUD,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hZD,←MonoidHom.range_eq_map,range_subtype,hspan]


/-- The same Sylow-fixed seed also gives reducedness for the actual C.2.7 actor LQ1. -/
theorem U_reduced_on_LQ1 (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    IsPReduced 2 ((d.U t).subgroupOf (d.L ⊔ d.Q1)) := by
  let := hi.quasisimple
  let := d.U_elementary s hG hM hu h hi hf t ht
  let D := d.L ⊔ d.S
  let J := d.L ⊔ d.Q1
  have hQ1S := d.Q1_le_S s hu
  have hJD : J ≤ D := sup_le le_sup_left (hQ1S.trans le_sup_right)
  have hUJ : d.U t ≤ J := (d.U_le_Q1 s hG hM hu h hi hf t ht).trans le_sup_right
  have hUD := hUJ.trans hJD
  have hZJ : d.Z2 t ≤ J := (le_conjugateSpanBy _ _).trans hUJ
  have hUJn : J ≤ normalizer (d.U t : Set G) := hJD.trans
    ((normal_subgroupOf_iff_le_normalizer hUD).mp (d.U_reduced s hG hM hu h hi hf t ht).normal)
  have hSJ : d.S ≤ normalizer (J : Set G) :=
    (le_inf (d.S_le_G1.trans (d.G1_normalizes_L hG h hf))
      (d.S_le_T.trans s.sylow_normalizes_Q1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup d.L d.Q1)
  let : (J.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (le_sup_left.trans J.le_normalizer) hSJ)
  have hsD := s.centralizer_sylow.restrict (show d.S ≤ D from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hsD hJD
    (inferInstance : (J.subgroupOf D).Normal).isSubnormal
  let W := (d.U t).subgroupOf J
  let Z0 := (d.Z2 t).subgroupOf J
  let : W.Normal := normal_subgroupOf_of_le_normalizer hUJn
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUJ
  refine ⟨inferInstance,inferInstance,
    centralizer_quotient_pCore_eq_bot_of_sylow_fixed_span W Z0 P
      (comap_mono (le_conjugateSpanBy _ _)) ?_ ?_⟩
  · intro z hz p hp
    exact Subtype.ext ((d.Z2_le_centralizer_S s t ht) hz p
      ((show (p : G) ∈ d.S ⊓ J from hP ▸ mem_map_of_mem J.subtype hp).1))
  · apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hUJ,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hZJ,←MonoidHom.range_eq_map,range_subtype]
    exact conjugateSpanBy_mono le_rfl le_sup_left

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
