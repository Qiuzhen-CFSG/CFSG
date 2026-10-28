module
public import Theory.GroupTheory.Fitting.TwoCorePreimage
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.OrderedSolvable
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
/-!
# The full C.2.6 ordered Fitting-preimage decomposition

Let F = O₂,F(G), and let R be radical. The preceding lower theorem makes R
Sylow in F R and proves that this join is solvable. The original hypothesis
F*(F) = O₂(G) makes the join characteristic two. Apply the genuine solvable
local C(G,T) theorem there. Every chosen A₃-block is two-perfect, hence lies
in F because F R/F is a two-group. Subnormality then lifts through normal F,
and the actual ordered factorization restricts from F R to F.

Thus both conclusions of C.2.6 hold for the original groups and inclusions;
no solvability of G, selected block, or product decomposition is assumed.
Source: Aschbacher–Smith C.2.6, printed p.145 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

theorem fitting_core_eq_of_source
    (hf : (generalizedFitting (twoFittingCore G)).map (twoFittingCore G).subtype = pCore 2 G) :
    generalizedFitting (twoFittingCore G) = pCore 2 (twoFittingCore G) := by
  apply map_injective (twoFittingCore G).subtype_injective
  rw [hf, pCore_subnormal_eq_comap 2 (inferInstance : (twoFittingCore G).Normal).isSubnormal]
  exact (map_comap_eq_self (show pCore 2 G ≤ (twoFittingCore G).subtype.range by
    rw [range_subtype]; exact twoCore_le_twoFittingCore)).symm

theorem fitting_ordered_product
    {κ : GroupClass} (hG : IsSQTK κ G)
    (R M : Subgroup G) (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hf : (generalizedFitting (twoFittingCore G)).map (twoFittingCore G).subtype = pCore 2 G) :
    ∃ n : ℕ, n ≤ 2 ∧ ∃ L : Fin n → Subgroup G,
      (∀ i, L i ≤ twoFittingCore G ∧ ¬ L i ≤ M ∧ IsBlock (L i) ∧ IsAlternatingBlock (L i) 3) ∧
      ∀ x : G, x ∈ twoFittingCore G ↔
        ∃ m ∈ M ⊓ twoFittingCore G, ∃ l : Fin n → G,
          (∀ i, l i ∈ L i) ∧ x = m * (List.ofFn l).prod := by
  let F := twoFittingCore G
  let D := F ⊔ R
  have hFD : F ≤ D := le_sup_left
  have hRD : R ≤ D := le_sup_right
  let : Group.IsSolvable D := twoFittingCore_sup_solvable R hr.isPGroup
  have hcF : centralizer (pCore 2 F : Set F) ≤ pCore 2 F :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mp (fitting_core_eq_of_source hf)
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
  have hLi (i) : L i ≤ F ∧ ¬ L i ≤ M ∧ IsBlock (L i) ∧ IsAlternatingBlock (L i) 3 := by
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
    exact ⟨hLF i, fun hLM => hout i (map_le_iff_le_comap.mp hLM),
      ⟨inferInstance,ha.2.1,Subgroup.IsSubnormal.trans (hLF i) hsub (inferInstance : F.Normal).isSubnormal⟩,ha⟩
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
