module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Two-core control for stabilizers of a normal chain

Let Q be a normal self-centralizing two-subgroup and J a normal subgroup.
The elements centralizing J and acting trivially on Q modulo J form a normal
two-group. Their two-residual D satisfies [Q,D,D] = [Q,D], but the chain
conditions make [Q,D,D] trivial. Thus D centralizes Q, lies in Q, and is
both two-perfect and a two-group, so is trivial.

The relative form keeps N, Q, J and E as literal ambient subgroups.
A final Sylow-kernel lemma identifies O2(N) from the original relative
Sylow condition and the trivial two-core of N/(I intersect N).
Source: GLS, Number 2, G.12.5 as used in G.26.18(a), printed pp.152–153.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem chain_centralizer_le_twoCore
    (Q J : Subgroup G) [Q.Normal] [J.Normal] (hQ : IsPGroup 2 Q)
    (hself : centralizer (Q : Set G) ≤ Q) :
    centralizer (J : Set G) ⊓ commutatorPreimage ⊤ Q J ≤ pCore 2 G := by
  let U := centralizer (J : Set G) ⊓ commutatorPreimage ⊤ Q J
  have hn : (commutatorPreimage (⊤ : Subgroup G) Q J).Normal := by
    rw [←normalizer_eq_top_iff]
    exact top_unique (commutatorPreimage_normalized ⊤ Q J ⊤
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal)
  let := hn
  let : U.Normal := inferInstance
  let D := (pResidual 2 U).map U.subtype
  have hDU : D ≤ U := map_subtype_le _
  have hD : IsPPerfect 2 D := isPPerfect_embedded_pResidual 2 U
  have hDJ : D ≤ centralizer (J : Set G) := hDU.trans inf_le_left
  have hQDJ : ⁅Q,D⁆ ≤ J := by
    rw [commutator_comm]
    exact (commutator_mono (hDU.trans inf_le_right) le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ Q J le_normalizer_of_normal)
  have hid := commutator_isPPerfect_idempotent D Q hD hQ le_normalizer_of_normal
  have hzero : ⁅Q,D⁆ = ⊥ := by
    apply bot_unique
    rw [←hid]
    exact (commutator_mono hQDJ le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hDJ)).le
  have hDQ : D ≤ Q := (commutator_eq_bot_iff_le_centralizer.mp
    (by rwa [commutator_comm] : ⁅D,Q⁆ = ⊥)).trans hself
  have hdp : IsPGroup 2 D := hQ.to_le hDQ
  have he : (⊥ : Subgroup D) = ⊤ := hD _ inferInstance
    (hdp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _))
  have hDbot : D = ⊥ := by
    apply bot_unique
    intro d hd
    exact congrArg Subtype.val (mem_bot.mp
      (show (⟨d,hd⟩ : D) ∈ (⊥ : Subgroup D) from he.symm ▸ mem_top _))
  have hres : pResidual 2 U = ⊥ := (map_eq_bot_iff_of_injective _ U.subtype_injective).mp hDbot
  have hp : IsPGroup 2 U := by
    have hh := isPGroup_quotient_pResidual (G := U) 2
    exact hh.of_equiv ((QuotientGroup.quotientMulEquivOfEq hres).trans QuotientGroup.quotientBot)
  exact le_sSup ⟨inferInstance,hp⟩
end Theory.GroupTheory

namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem le_twoCore_of_relative_chain (N Q J E : Subgroup G)
    (hQN : Q ≤ N) (hJN : J ≤ N) (hEN : E ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) (hNJ : N ≤ normalizer (J : Set G))
    (hQ : IsPGroup 2 Q) (hself : N ⊓ centralizer (Q : Set G) ≤ Q)
    (hEJ : E ≤ centralizer (J : Set G)) (hcomm : ⁅E,Q⁆ ≤ J) :
    E ≤ N.pCoreIn 2 := by
  let Q' := Q.subgroupOf N
  let J' := J.subgroupOf N
  let E' := E.subgroupOf N
  let : Q'.Normal := normal_subgroupOf_of_le_normalizer hNQ
  let : J'.Normal := normal_subgroupOf_of_le_normalizer hNJ
  have hs : centralizer (Q' : Set N) ≤ Q' := by
    intro n hn
    apply hself
    refine ⟨n.property,?_⟩
    intro q hq
    exact congrArg Subtype.val (mem_centralizer_iff.mp hn ⟨q,hQN hq⟩ hq)
  have hc : E' ≤ centralizer (J' : Set N) := by
    intro e he j hj
    exact Subtype.ext (hEJ he j hj)
  have hd : ⁅E',Q'⁆ ≤ J' := by
    apply (map_le_map_iff_of_injective (f := N.subtype) N.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hEN,map_subgroupOf_eq_of_le hQN,
      map_subgroupOf_eq_of_le hJN]
    exact hcomm
  have hE : E' ≤ pCore 2 N := (le_inf hc (le_commutatorPreimage le_top hd)).trans
    (chain_centralizer_le_twoCore Q' J' hQ.comap_subtype hs)
  have hm := map_mono (f := N.subtype) hE
  rwa [map_subgroupOf_eq_of_le hEN] at hm
end Theory.GroupTheory


public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A Sylow subgroup of the kernel, normalized by N, is O2(N) when the
quotient by the kernel has trivial two-core. The kernel is I intersect N;
I need not be contained in N. -/
theorem pCoreIn_eq_of_normalized_sylow_and_coreFree_quotient
    (N I Q : Subgroup G) [(I.subgroupOf N).Normal]
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = Q)
    (hQN : Q ≤ N) (hNQ : N ≤ normalizer (Q : Set G))
    (hcore : pCore 2 (N ⧸ I.subgroupOf N) = ⊥) : N.pCoreIn 2 = Q := by
  obtain ⟨P,hP⟩ := hSyl
  have hQ : IsPGroup 2 Q := hP ▸ P.isPGroup'.map I.subtype
  have hQI : Q ≤ I := hP ▸ map_subtype_le _
  let C := N.pCoreIn 2
  let q := QuotientGroup.mk' (I.subgroupOf N)
  have hm : (pCore 2 N).map q ≤ pCore 2 (N ⧸ I.subgroupOf N) :=
    le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective _),pCore_isPGroup.map q⟩
  have hCI : C ≤ I := by
    rintro _ ⟨c,hc,rfl⟩
    have hz := hm (mem_map_of_mem q hc)
    rw [hcore,mem_bot] at hz
    exact (QuotientGroup.eq_one_iff c).mp hz
  have hNC : N ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro n hn c hc
    obtain ⟨c',hc',rfl⟩ := hc
    exact mem_map_of_mem N.subtype ((inferInstance : (pCore 2 N).Normal).conj_mem
      c' hc' (⟨n,hn⟩ : N))
  have hp : IsPGroup 2 (Q ⊔ C : Subgroup G) :=
    hQ.to_sup_of_normal_right' (isPGroup_pCoreIn 2 N) (hQN.trans hNC)
  have he : (Q ⊔ C).subgroupOf I = (P : Subgroup I) :=
    P.is_maximal' hp.comap_subtype (by
      intro x hx
      exact mem_sup_left (hP ▸ mem_map_of_mem I.subtype hx))
  apply le_antisymm _ (le_pCoreIn_of_normalizes hQ hQN hNQ)
  intro c hc
  have hh : (⟨c,hCI hc⟩ : I) ∈ (P : Subgroup I) :=
    he ▸ (show (⟨c,hCI hc⟩ : I) ∈ (Q ⊔ C).subgroupOf I from mem_sup_right hc)
  exact hP ▸ mem_map_of_mem I.subtype hh
end Theory.GroupTheory
