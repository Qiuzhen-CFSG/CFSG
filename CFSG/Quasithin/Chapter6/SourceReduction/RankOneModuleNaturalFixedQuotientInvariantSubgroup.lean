module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSectionBudget

/-!
# The original input on a noncentral invariant subgroup

Every noncentral LT-invariant subgroup of the original reduced module has
exactly the same two-core centralizer. In LT/O₂(LT), a normal kernel either
contains the quasisimple component or centralizes it. Noncentrality rules out
the first possibility and the component's trivial centralizer rules out the
second. The subgroup is therefore reduced and carries the original input.

This permits selection inside the canonical deleted-A₅ complement without
assuming that complement is reduced or faithful.
Source: Aschbacher--Smith 5.1.3, printed pp.630--631.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W U : Subgroup G} {n : ℕ}

/-- A noncentral invariant subgroup retains all of the original rank-one
input, including reducedness; no representation kernel premise is needed. -/
theorem Input.invariant_subgroup_input
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hUW : U ≤ W) (hLU : L ≤ normalizer (U : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hnon : ⁅U,L⁆ ≠ ⊥) : Input KnownSimple.IsKnownSimple T L U n := by
  let J := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf J
  let U₀ := U.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hUJ : U ≤ J := hUW.trans h.reduced.1
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le hLU hTU)
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  let C := centralizer (U₀ : Set J)
  let Q := J ⧸ pCore 2 J
  let q : J →* Q := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let K := B.map q
  let : K.Normal := (inferInstance : B.Normal).map q hq
  let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eqB := QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)
  let := h.quotient_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eqB.symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv (coreQuotientEquivImage 2 B)
  let eK : K ≃* (L ⧸ pCore 2 L) := (coreQuotientEquivImage 2 B).symm.trans eqB
  have hsup : B ⊔ (S : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  have htwo : IsPGroup 2 (Q ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K ((S : Subgroup J).map q) (S.isPGroup'.map q) (by
      rw [←Subgroup.map_sup,hsup,map_top_of_surjective q hq])
  have hz : center K = ⊥ := by
    apply bot_unique
    intro x hx
    apply eK.map_eq_one_iff.mp
    exact h.quotient_center_eq_bot.le (MulEquivClass.apply_mem_center eK hx)
  have hCK : centralizer (K : Set Q) = ⊥ :=
    (centralizer_eq_twoCore_of_centerless_quasisimple_quotient K hz htwo).trans
      (pCore_quotient_pCore_eq_bot 2)
  have hkerC : q.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    exact h.reduced_centralizer_eq_twoCore.ge.trans
      (centralizer_le (show U₀ ≤ W.subgroupOf J from fun _ hx => hUW hx))
  have hKC : ¬ K ≤ C.map q := by
    intro hle
    apply hnon
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro l hl u hu
    let l₀ : J := ⟨l,(show L ≤ J from le_sup_left) hl⟩
    have hlC : l₀ ∈ C := by
      have hm := hle (mem_map_of_mem q (show l₀ ∈ B from hl))
      have hh : l₀ ∈ (C.map q).comap q := hm
      rw [comap_map_eq_self hkerC] at hh
      exact hh
    exact congrArg J.subtype (hlC ⟨u,hUJ hu⟩ hu)
  let : (C.map q).Normal := (inferInstance : C.Normal).map q hq
  have hcomp : IsComponent Q K :=
    ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  have hmap : C.map q = ⊥ := by
    rcases hcomp.normal_dichotomy (C.map q) with hle | hc
    · exact (hKC hle).elim
    · apply bot_unique
      exact (commutator_eq_bot_iff_le_centralizer.mp
        ((commutator_comm _ _).trans hc)).trans hCK.le
  have hqker : q.ker = pCore 2 J := QuotientGroup.ker_mk' _
  have hC : C = pCore 2 J := by
    apply le_antisymm
    · have hh := (Subgroup.map_eq_bot_iff C).mp hmap
      simpa only [hqker] using hh
    · simpa only [hqker] using hkerC
  have hred : U ∈ reducedFamily J := by
    let := h.reduced.2.1
    refine ⟨hUJ,IsElementaryAbelian.of_le hUW,⟨inferInstance,?_⟩⟩
    let e := QuotientGroup.quotientMulEquivOfEq hC
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso 2 e,Subgroup.map_bot]
    exact pCore_quotient_pCore_eq_bot 2
  exact { h with reduced := hred, noncentral := hnon }

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
