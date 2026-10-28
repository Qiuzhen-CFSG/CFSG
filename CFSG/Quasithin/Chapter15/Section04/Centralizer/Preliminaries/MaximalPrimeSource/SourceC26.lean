module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.FittingProduct
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SourceInputs
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.Fitting.OutsideComponent
/-!
# Discharging the genuine universal C.2.6 source input

Transport the proved intrinsic Fitting-preimage decomposition through the
original inclusion H → G. The Sylow subgroup, each outside A₃-block, relative
subnormality in H and the ordered setwise product use these literal maps.
This proves the existing EarlierC26 contract in full; no assumption of
ambient solvability or selected blocks remains.

Source: Aschbacher–Smith C.2.6, p.145, used in 15.4.3, p.1157.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem earlierC26_source : EarlierC26.{u} := by
  intro G _ _ H R M hsetup hf
  let F := twoFittingCore H
  have hFI : F.map H.subtype = twoFittingPreimage H := rfl
  let e : F ≃* twoFittingPreimage H := equivMapOfInjective F H.subtype H.subtype_injective
  have hfin : (generalizedFitting F).map F.subtype = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [map_map]
    rw [← map_generalizedFitting_equiv e,map_map] at hf
    exact hf
  have hs := twoFittingCore_sup_sylow (R.subgroupOf H) hsetup.radical
  let D := F ⊔ R.subgroupOf H
  change ∃ S : Sylow 2 D, (S : Subgroup D).map D.subtype = R.subgroupOf H at hs
  obtain ⟨S,hS⟩ := hs
  have hmap : D.map H.subtype = twoFittingPreimage H ⊔ R := by
    rw [Subgroup.map_sup,hFI,map_subgroupOf_eq_of_le hsetup.radical_le]
  let eD : D ≃* (twoFittingPreimage H ⊔ R : Subgroup G) :=
    (equivMapOfInjective D H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  constructor
  · refine ⟨S.mapSurjective (f := eD.toMonoidHom) eD.surjective, ?_⟩
    change ((S : Subgroup D).map eD.toMonoidHom).map (twoFittingPreimage H ⊔ R).subtype = R
    rw [map_map]
    have hh := congrArg (map H.subtype) hS
    rw [map_map,map_subgroupOf_eq_of_le hsetup.radical_le] at hh
    exact hh
  · intro _hout
    obtain ⟨n,_hn,B,hB,hprod⟩ := ChapterC.Section02Source.fitting_ordered_product
      hsetup.sqtk (R.subgroupOf H) (M.subgroupOf H)
      hsetup.radical hsetup.characteristic_control hfin
    let L (i : Fin n) : Subgroup G := (B i).map H.subtype
    have hLF (i) : L i ≤ twoFittingPreimage H := map_mono (hB i).1
    have hLi (i) : L i ≤ twoFittingPreimage H ∧ ¬ L i ≤ M ∧
        ChapterC.IsBlock ((L i).subgroupOf H) ∧ ChapterC.IsAlternatingBlock (L i) 3 := by
      refine ⟨hLF i, fun hLM => (hB i).2.1 (map_le_iff_le_comap.mp hLM), ?_, ?_⟩
      · simpa only [L,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using (hB i).2.2.1
      · exact ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
          (equivMapOfInjective (B i) H.subtype H.subtype_injective) (hB i).2.2.2
    refine ⟨n,L,hLi,fun x => ⟨?_,?_⟩⟩
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨m,hm,l,hl,he⟩ := (hprod x).mp hx
      refine ⟨m,⟨hm.1,mem_map_of_mem H.subtype hm.2⟩,fun i => l i,
        fun i => mem_map_of_mem H.subtype (hl i),?_⟩
      have hh := congrArg H.subtype he
      simpa only [map_mul,map_list_prod,List.map_ofFn,Function.comp_def,Subgroup.coe_subtype] using hh
    · rintro ⟨m,hm,l,hl,rfl⟩
      apply (twoFittingPreimage H).mul_mem hm.2
      apply (twoFittingPreimage H).list_prod_mem
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact hLF i (hl i)
/-- The actual ambient preimages extract an outside C-component with the
quasisimple two-core quotient and characteristic-two structure used in 13.3.12. -/
theorem outside_component_of_fitting_preimage_control (H M : Subgroup G)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hf : twoFittingPreimage H ≤ M)
    (hg : ¬ ChapterA.Section04.twoGeneralizedFittingPreimage H ≤ M) :
    ∃ L : Subgroup G, L ≤ H ∧ (L.subgroupOf H).IsCComponent ∧
      IsQuasisimple (L ⧸ pCore 2 L) ∧ generalizedFitting L = pCore 2 L ∧ ¬ L ≤ M := by
  have hfin : twoFittingCore H ≤ M.subgroupOf H := map_le_iff_le_comap.mp hf
  have hgin : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
    intro hh
    exact hg (map_le_iff_le_comap.mpr hh)
  obtain ⟨B,hB,hq,hchar,hout⟩ := exists_characteristicTwo_cComponent_outside
    (M.subgroupOf H) hc hfin hgin
  let L := B.map H.subtype
  let e : B ≃* L := equivMapOfInjective B H.subtype H.subtype_injective
  have hsub : (L.subgroupOf H).IsCComponent := by
    simpa only [L,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hB
  let : IsQuasisimple (B ⧸ pCore 2 B) := hq
  have hqL : IsQuasisimple (L ⧸ pCore 2 L) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hfL : generalizedFitting L = pCore 2 L := by
    rw [← map_generalizedFitting_equiv e, hchar,pCore_map_iso 2 e]
  exact ⟨L,map_subtype_le _,hsub,hqL,hfL,fun hLM => hout (map_le_iff_le_comap.mp hLM)⟩

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
