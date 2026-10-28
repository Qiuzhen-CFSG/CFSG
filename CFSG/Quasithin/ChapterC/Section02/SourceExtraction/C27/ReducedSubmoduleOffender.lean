module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.GroupTheory.ReducedNormal.Defs
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore
/-!
# Best offenders on a specified reduced C.2.7 submodule

A reduced noncentral normal submodule contained in the original radical has
the same two-core centralizer intersection as the full star module. C.2.7's
Thompson escape therefore supplies an actual maximum elementary subgroup
whose nontrivial image is a best offender on this submodule.

Source: Aschbacher--Smith C.2.7(2), B.2.5 and 15.1.28, pp.76,146,1103.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.StarSelection
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass} {H K R M : Subgroup G}
/-- C.2.7's actual radical supplies a best offender on a reduced noncentral
submodule inside R, not only on the full omega-center. -/
theorem best_offender_on_reduced_submodule (hi : Input κ H R M K)
    (W : Subgroup (K ⊔ R : Subgroup G)) [W.Normal] [IsElementaryAbelian 2 W]
    (hr : IsPReduced 2 W) (hWR : W ≤ R.subgroupOf (K ⊔ R))
    (hm : ⁅W,K.subgroupOf (K ⊔ R)⁆ ≠ ⊥) :
    let q := QuotientGroup.mk' (centralizer (W : Set (K ⊔ R : Subgroup G)))
    ∃ A : Subgroup (K ⊔ R : Subgroup G),
      A ∈ elementaryAbelianMaxSubgroups (R.subgroupOf (K ⊔ R)) ∧
      IsBestOffender (NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (A.map q) := by
  let J := K ⊔ R
  let K0 := K.subgroupOf J
  let R0 := R.subgroupOf J
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
  let e : K0 ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let := hi.quasisimple
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hp : IsPGroup 2 R := by
    have hh := hi.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le hi.setup.radical_le] at hh
  obtain ⟨P,hRP⟩ := hp.comap_subtype.exists_le_sylow (P := R0)
  have hgen : K0 ⊔ R0 = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),subgroupOf_self]
  have hprod : ∀ g : J, ∃ k ∈ K0, ∃ t ∈ (P : Subgroup J), k*t=g := by
    intro g
    obtain ⟨k,hk,t,ht,he⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
    exact ⟨k,hk,t,hRP ht,he⟩
  have hcore := (internalModule_quasisimple_core_structure W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hr.quotient_pCore_eq_bot P K0
    (hi.component.2.subgroupOf_of_le le_sup_left hi.join_le) inferInstance hm hprod).1
  have hth := (kernel_offender_from_source hi).2.thompson
  have hJ : ¬ elementaryAbelianMaxJ R0 ≤ C := by
    intro hh
    have hjR : elementaryAbelianMaxJ R0 ≤ R0 := sSup_le fun _ hA => hA.1
    have hjQ : elementaryAbelianMaxJ R0 ≤ pCore 2 J := (le_inf (hjR.trans hRP) hh).trans hcore.ge
    have hQR : pCore 2 J ≤ R0 := by
      let hiJ := source_join_input hi
      let : (K.subgroupOf J).Normal := inferInstanceAs K0.Normal
      exact fun x hx => source_joinCore_le_radical hiJ (mem_map_of_mem J.subtype hx)
    have he := elementaryAbelianMaxJ_eq_of_intermediate R0 (pCore 2 J) hjQ hQR
    have hh := congrArg (map J.subtype) he
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)] at hh
    exact hth hh.ge
  obtain ⟨A,hA,hne⟩ : ∃ A, A ∈ elementaryAbelianMaxSubgroups R0 ∧ ¬ A ≤ C := by
    by_contra! hh
    exact hJ (sSup_le hh)
  refine ⟨A,hA,maxElementary_isBestOffender W q (QuotientGroup.mk'_surjective C)
    (QuotientGroup.ker_mk' C) R0 A hWR hA ?_⟩
  intro hb
  exact hne (by
    have hh := (Subgroup.map_eq_bot_iff A).mp hb
    simpa only [show q.ker = C from QuotientGroup.ker_mk' C] using hh)

end CFSG.Quasithin.ChapterC.C27Source
