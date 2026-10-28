module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSevenExceptional
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenWeightTwo
-- Intentional same-package reuse of intrinsic point/coatom and radical-rank
-- helpers. No CaseIComponentData record or private name enters the public type.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenWeightTwo

/-! The original central-involution seed gives a literal block vector whose
centralizer is the original marked intersection. The actual C.2.7 radical
forces its weight to be two. All normalizers and quotient markings remain
on the same original local component; no generation hypothesis is used. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem raw_seven_point
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬K ≤ M)
    (hb : IsAlternatingBlock K 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    let N := centralizer (Z1 : Set G) ⊓ Mc
    let R := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ normalizer (K : Set G)
    ∃ E : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
      (∀ k u, E (blockConjugate K k u) =
        BinaryPermutation.SevenMarkedAction.coreAction
          (e (QuotientGroup.mk' (pCore 2 K) k)).val (E u)) ∧
      ∃ u : blockU K, u ≠ 1 ∧
        ((u : K) : G) ∈ centralizer (R : Set G) ∧
        N ⊓ K = K ⊓ centralizer ({((u : K) : G)} : Set G) ∧
        IsCoatom ((N ⊓ K).subgroupOf K) := by
  let N := centralizer (Z1 : Set G) ⊓ Mc
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (K : Set G)
  let U := (blockU K).map K.subtype
  let H := K ⊔ R
  have hHN : H ≤ normalizer (K : Set G) := sup_le le_normalizer inf_le_right
  have hHU : H ≤ normalizer (U : Set G) := hHN.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hUH : U ≤ H := (map_subtype_le _).trans le_sup_left
  have hUQ : U ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((pCore_isPGroup.to_le blockU_le_core).map K.subtype) hUH hHU
  obtain ⟨_,_,⟨P,hP⟩,_,hZR⟩ := h.raw_component_thompson hG T hM hJ hu hZ hK hq hb.2.1.fitting hout houtM
  have hUR : U ≤ R := hUQ.trans (by
    have hh := map_mono (f := H.subtype) (pCore_isPGroup.le_sylow_of_normal P)
    rw [hP] at hh
    exact hh)
  have hUT : U ≤ (T : Subgroup G) := hUR.trans (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left))
  have hMc : centralizer (centralInvolutions T : Set G) ≤ Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).2
  have hn : ¬ centralInvolutions T ≤ centralizer (K : Set G) := by
    intro hc
    exact hout (le_inf hK.1 ((le_centralizer_iff.mp hc).trans hMc))
  obtain ⟨z,hz,hzc⟩ := SetLike.not_le_iff_exists.mp hn
  have hz1 : z ≠ 1 := fun he => hzc (he ▸ one_mem _)
  have hzN : z ∈ normalizer (K : Set G) := (hZR hz).2
  have hzU : z ∈ centralizer (U : Set G) :=
    (centralizer_le hUT) (centralInvolutions_le_centralizer_sylow T hz)
  obtain ⟨u,huc⟩ := hb.seven_module_fixer_factorization hzN hzU
  have huU : ((u : K) : G) ∈ U := mem_map_of_mem K.subtype u.property
  have hu1 : u ≠ 1 := by
    intro he
    apply hzc
    simpa only [he,OneMemClass.coe_one,mul_one,one_mul] using huc
  have huR : ((u : K) : G) ∈ centralizer (R : Set G) := by
    intro r hr
    have hrN := hr.2
    have hrz : r*z*r⁻¹ = z := by
      rw [centralInvolutions_le_centralizer_sylow T hz r ((show S ≤ (T : Subgroup G) from inf_le_left) hr.1),mul_inv_cancel_right]
    have hu' : r * ((u : K) : G) * r⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (hHU (mem_sup_right hr)) _).mp huU
    have hc' : (r * ((u : K) : G) * r⁻¹) * z ∈ centralizer (K : Set G) := by
      have hh := (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer K hrN) _).mp huc
      have he : r * (((u : K) : G)*z) * r⁻¹ = (r*((u : K) : G)*r⁻¹)*z := by
        calc
          _ = (r*((u : K) : G)*r⁻¹)*(r*z*r⁻¹) := by group
          _ = _ := by rw [hrz]
      exact he ▸ hh
    have hd : ((u : K) : G) * (r * ((u : K) : G) * r⁻¹)⁻¹ ∈ centralizer (K : Set G) := by
      have hh := (centralizer (K : Set G)).mul_mem huc ((centralizer (K : Set G)).inv_mem hc')
      simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hh
    have hone := CaseIComponentData.seven_fixed_trivial hb (U.mul_mem huU (U.inv_mem hu')) hd
    have he := mul_inv_eq_one.mp hone
    exact (mul_inv_eq_iff_eq_mul.mp he.symm)
  have hCz : centralizer ({z} : Set G) ≤ Mc := by
    have hzp : IsPGroup 2 (zpowers z) :=
      T.isPGroup'.to_le ((zpowers_le.mpr hz).trans (centralInvolutions_le_sylow T))
    have hh := centralizer_le_of_unique_twoLocal hzp
      (fun he => hz1 (show z ∈ (⊥ : Subgroup G) from he ▸ mem_zpowers z))
      ((centralizer_le (show (zpowers z : Set G) ⊆ centralInvolutions T from
        zpowers_le.mpr hz)).trans (Subgroup.centralizer_le_normalizer _))
      (M := Mc) (by
        intro N hN hCN
        exact Set.mem_singleton_iff.mp (hu ▸ (show N ∈ maximalTwoLocalOvergroups
          (centralizer (centralInvolutions T : Set G)) from ⟨hN,hCN⟩)))
    apply le_trans ?_ hh
    rw [le_centralizer_iff, zpowers_le]
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hCu : K ⊓ centralizer ({((u : K) : G)} : Set G) ≤ N ⊓ K := by
    intro k hk
    refine ⟨⟨hK.1 hk.1,hCz ?_⟩,hk.1⟩
    apply mem_centralizer_singleton_iff.mpr
    have hc := huc k hk.1
    have hku := mem_centralizer_singleton_iff.mp hk.2
    symm
    calc
      z*k = ((u : K) : G)⁻¹ * ((((u : K) : G)*z)*k) := by group
      _ = ((u : K) : G)⁻¹ * (k*(((u : K) : G)*z)) := by rw [hc]
      _ = k*z := by rw [←mul_assoc k,hku]; group
  obtain ⟨E,hE⟩ := hb.seven_module_coordinates_at e
  have hc := CaseIComponentData.seven_point_coatom e E hE u hu1
  have hproper : (N ⊓ K).subgroupOf K ≠ ⊤ := by
    intro he
    exact hout fun k hk => (he.ge (show (⟨k,hk⟩ : K) ∈ ⊤ from mem_top _)).1
  have he : (N ⊓ K).subgroupOf K = (centralizer ({((u : K) : G)} : Set G)).comap K.subtype :=
    (hc.le_iff_eq hproper).mp (fun k hk => hCu ⟨k.property,hk⟩)
  refine ⟨E,hE,u,hu1,huR,?_,he.symm ▸ hc⟩
  ext k
  constructor
  · intro hk
    refine ⟨hk.2,?_⟩
    change (⟨k,hk.2⟩ : K) ∈ (centralizer ({((u : K) : G)} : Set G)).comap K.subtype
    rw [←he]
    exact hk
  · intro hk
    exact hCu hk

/-- The same original marked intersection is the centralizer of an actual
weight-two vector under the prescribed whole-block quotient marking. -/
theorem PreparedChosenModule.raw_seven_weight_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬K ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) K)
    (hb : IsAlternatingBlock K 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    let N := centralizer (Z1 : Set G) ⊓ Mc
    let R := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ normalizer (K : Set G)
    ∃ E : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
      (∀ k u, E (blockConjugate K k u) =
        BinaryPermutation.SevenMarkedAction.coreAction
          (e (QuotientGroup.mk' (pCore 2 K) k)).val (E u)) ∧
      ∃ u : blockU K, BinarySevenCode.weight (E u).toAdd.val = 2 ∧
        ((u : K) : G) ∈ centralizer (R : Set G) ∧
        N ⊓ K = K ⊓ centralizer ({((u : K) : G)} : Set G) ∧
        IsCoatom ((N ⊓ K).subgroupOf K) := by
  let N := centralizer (Z1 : Set G) ⊓ Mc
  obtain ⟨E,hE,u,hu1,huc,heq,hmax⟩ := raw_seven_point hG T hM hJ hu h hZ hK
    hi.quasisimple hi.outside houtM hb e
  have hr := CaseIComponentData.seven_radical_normalizer_rank hi hb (D := N ⊓ K) inf_le_right
    (inf_le_left.trans (N.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
  have he : ((N ⊓ K).subgroupOf K) =
      (centralizer ({((u : K) : G)} : Set G)).comap K.subtype := by
    ext k
    change (k : G) ∈ N ⊓ K ↔ (k : G) ∈ centralizer ({((u : K) : G)} : Set G)
    rw [heq]
    exact and_iff_right k.property
  have hri : primeRank 3 ((centralizer ({((u : K) : G)} : Set G)).comap K.subtype) ≤ 1 := by
    rw [←he,primeRank_congr 3 (subgroupOfEquivOfLe (show N ⊓ K ≤ K from inf_le_right))]
    exact hr
  exact ⟨E,hE,u,CaseIComponentData.seven_point_weight_two e E hE u hu1 hri,huc,heq,hmax⟩

end CFSG.Quasithin.Chapter15.Section01
