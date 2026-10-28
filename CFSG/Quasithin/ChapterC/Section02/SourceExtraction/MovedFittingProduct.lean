module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.FittingProduct
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# C.2.6 with the original Thompson movement retained

The solvable C.2.6 decomposition is transported from O₂,F(G)R to G while
retaining each outside block's literal identity X=[X,J(R)]. This identity
is required when applying 14.1.10 to the exceptional branch of 14.1.13;
the ordered factorization alone does not provide that hypothesis.

Source: Aschbacher–Smith C.2.6 and 14.1.13, printed pp.145 and 979.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

theorem fitting_ordered_moved_product
    {κ : GroupClass} (hG : IsSQTK κ G)
    (R M : Subgroup G) (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hcG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    ∃ n : ℕ, n ≤ 2 ∧ ∃ L : Fin n → Subgroup G,
      (∀ i, L i ≤ twoFittingCore G ∧ ¬ L i ≤ M ∧ IsBlock (L i) ∧ IsAlternatingBlock (L i) 3 ∧
        L i = ⁅L i, Stellmacher.elementaryAbelianMaxJ R⁆) ∧
      ∀ x : G, x ∈ twoFittingCore G ↔
        ∃ m ∈ M ⊓ twoFittingCore G, ∃ l : Fin n → G,
          (∀ i, l i ∈ L i) ∧ x = m * (List.ofFn l).prod := by
  let F := twoFittingCore G
  let D := F ⊔ R
  have hFD : F ≤ D := le_sup_left
  have hRD : R ≤ D := le_sup_right
  let : Group.IsSolvable D := twoFittingCore_sup_solvable R hr.isPGroup
  have hcF : centralizer (pCore 2 F : Set F) ≤ pCore 2 F :=
    subnormal_core_selfCentralizing hcG F (inferInstance : F.Normal).isSubnormal
  have hfD : generalizedFitting D = pCore 2 D :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (twoFittingCore_sup_characteristicTwo R hr.isPGroup hcF)
  have hs := twoFittingCore_sup_sylow R hr
  change ∃ S : Sylow 2 D, (S : Subgroup D).map D.subtype = R at hs
  obtain ⟨S,hS⟩ := hs
  have hSM : (S : Subgroup D) = R.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hRD]
  have hc : (S : Subgroup D).characteristicNormalizerClosure ≤ M.subgroupOf D := by
    rw [hSM]
    exact characteristicNormalizerClosure_subgroupOf_le hRD hcontrol
  obtain ⟨n,hn,B,hB,hout,hmove,hprod⟩ := ordered_alternatingThree_product
    (inferInstance : Group.IsSolvable D) (hG.subgroup D) hfD S (M.subgroupOf D) hc
  let FD := F.subgroupOf D
  let : FD.Normal := inferInstance
  have hgen : FD ⊔ R.subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup hFD hRD, subgroupOf_self]
  have hquot : IsPGroup 2 (D ⧸ FD) :=
    isPGroup_quotient_of_sup_eq_top FD (R.subgroupOf D) hr.isPGroup.comap_subtype hgen
  have hBF (i) : B i ≤ FD := by
    have ht := (hB i).1.short.twoPerfect.hom_eq_one_of_isPGroup hquot
      ((QuotientGroup.mk' FD).comp (B i).subtype)
    intro b hbb
    exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun ht ⟨b, hbb⟩)
  let L (i : Fin n) : Subgroup G := (B i).map D.subtype
  have hLF (i) : L i ≤ F := by
    rintro _ ⟨b,hb,rfl⟩
    exact hBF i hb
  have hLi (i) : L i ≤ F ∧ ¬ L i ≤ M ∧ IsBlock (L i) ∧
      IsAlternatingBlock (L i) 3 ∧ L i = ⁅L i, Stellmacher.elementaryAbelianMaxJ R⁆ := by
    let e : B i ≃* L i := equivMapOfInjective (B i) D.subtype D.subtype_injective
    have ha : IsAlternatingBlock (L i) 3 :=
      RankOne.Solvable.isAlternatingBlock_of_equiv e (hB i).2
    have hsub : ((L i).subgroupOf F).IsSubnormal := by
      have he : (B i).comap (inclusion hFD) = (L i).subgroupOf F := by
        ext x
        change (⟨(x : G), hFD x.property⟩ : D) ∈ B i ↔ (x : G) ∈ (B i).map D.subtype
        exact (mem_map_iff_mem D.subtype_injective).symm
      rw [← he]
      exact (hB i).1.subnormal.comap (inclusion hFD)
    refine ⟨hLF i, fun hLM => hout i (map_le_iff_le_comap.mp hLM),
      ⟨inferInstance,ha.2.1,Subgroup.IsSubnormal.trans (hLF i) hsub (inferInstance : F.Normal).isSubnormal⟩,ha, ?_⟩
    have hh := congrArg (map D.subtype) (hmove i)
    rw [map_commutator, ← Stellmacher.elementaryAbelianMaxJ_map_injective
      D.subtype D.subtype_injective, hS] at hh
    exact hh
  refine ⟨n,hn,L,hLi,fun x => ⟨?_,?_⟩⟩
  · intro hx
    obtain ⟨m,b,hxprod⟩ := hprod ⟨x,hFD hx⟩
    let l : Fin n → G := fun i => (b i : D)
    have hl (i) : l i ∈ L i := mem_map_of_mem D.subtype (b i).property
    have hprodF : (List.ofFn l).prod ∈ F := by
      apply F.list_prod_mem
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact hLF i (hl i)
    have he : x = ((m : D) : G) * (List.ofFn l).prod := by
      have hh := congrArg D.subtype hxprod
      simpa only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, Subgroup.coe_subtype, l] using hh
    refine ⟨m,⟨m.property,?_⟩,l,hl,he⟩
    have hh := F.mul_mem hx (F.inv_mem hprodF)
    rw [he,mul_inv_cancel_right] at hh
    exact hh
  · rintro ⟨m,hm,l,hl,rfl⟩
    apply F.mul_mem hm.2
    apply F.list_prod_mem
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact hLF i (hl i)
end CFSG.Quasithin.ChapterC.Section02Source
