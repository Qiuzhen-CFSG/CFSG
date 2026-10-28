module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ShortAction
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.FittingProduct
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
/-!
# The Fitting preimage lies in the original C.2.8 local subgroup

The odd core of H is trivial, so the solvable Fitting preimage above O₂(H)
has characteristic two. The ordered C.2.6 decomposition supplies only A₃
blocks outside M. Its actual chi-block family has at most two members;
the perfect span of L therefore normalizes each block. The cyclic quotient
of an A₃ block makes the perfect action trivial. The original module and
its normalizer bound exclude every such outside block.

Source: Aschbacher–Smith C.2.11, printed p.148 (`refs/quasithin.pdf`).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
private theorem cyclic_short_centralized (K B : Subgroup G) [K.Normal] [Group.IsPerfect B]
    (hK : IsShort K) [IsCyclic (K ⧸ pCore 2 K)] : ⁅K,B⁆ = ⊥ := by
  let f : B →* MulAut (K ⧸ pCore 2 K) :=
    (normalQuotientAction K (pCore 2 K)).comp B.subtype
  let _ := (IsCyclic.mulAutMulEquiv (K ⧸ pCore 2 K)).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv (K ⧸ pCore 2 K)).injective
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hf (b : B) : f b = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨f b,b,rfl⟩ : f.range) 1)
  apply SourceShortAction.perfect_centralizes_short_of_normalizes K B hK le_normalizer_of_normal
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb k hk
  let v : K := ⟨k,hk⟩
  have he := DFunLike.congr_fun (hf ⟨b,hb⟩) (QuotientGroup.mk' (pCore 2 K) v)
  simp only [f,MonoidHom.comp_apply,normalQuotientAction_apply_mk,
    MulAut.one_apply] at he
  have hh := QuotientGroup.eq_iff_div_mem.mp he
  refine ⟨(MulAut.conjNormal b v) / v,hh,?_⟩
  simp [v,div_eq_mul_inv,commutatorElement_def]

private theorem a3_centralized (K B : Subgroup G) [Group.IsPerfect B]
    (hK : IsAlternatingBlock K 3) (hBK : B ≤ normalizer (K : Set G)) : ⁅K,B⁆ = ⊥ := by
  let N := normalizer (K : Set G)
  let K' := K.subgroupOf N
  let B' := B.subgroupOf N
  let : K'.Normal := (normal_subgroupOf_iff_le_normalizer K.le_normalizer).mpr le_rfl
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBK).symm.surjective
  have hk := RankOne.Solvable.isAlternatingBlock_of_equiv
    (subgroupOfEquivOfLe K.le_normalizer).symm hK
  have hc : Nat.card (K' ⧸ pCore 2 K') = 3 := by
    obtain ⟨e⟩ := hk.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  let : IsCyclic (K' ⧸ pCore 2 K') := isCyclic_of_prime_card hc
  have he := congrArg (map N.subtype) (cyclic_short_centralized K' B' hk.2.1)
  have hkmap : K'.map N.subtype = K := map_subgroupOf_eq_of_le K.le_normalizer
  have hbmap : B'.map N.subtype = B := map_subgroupOf_eq_of_le hBK
  rwa [map_commutator,hkmap,hbmap,Subgroup.map_bot] at he

variable {κ : GroupClass} {H M L R V : Subgroup G}
private theorem fitting_preimage_fitting (h : HypothesisC28 κ H M L R V) :
    generalizedFitting (twoFittingCore H) = pCore 2 (twoFittingCore H) := by
  let : Group.IsSolvable (twoFittingCore H) := twoFittingCore_solvable
  have he : componentLayer (twoFittingCore H) = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    let := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  rw [generalizedFitting,he,sup_bot_eq,Fitting_eq_pcore _ 2
    ((inferInstance : (twoFittingCore H).Normal).isSubnormal.pPrimeCore_eq_bot h.oddCore_eq_bot _)]

/-- C.2.11 for the original C.2.8 input. -/
theorem fitting_preimage_le (h : HypothesisC28 κ H M L R V) :
    twoFittingCore H ≤ M.subgroupOf H := by
  let F := twoFittingCore H
  let A := (conjugateSpanBy L M).subgroupOf H
  have hAH : conjugateSpanBy L M ≤ H :=
    (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAH).symm.surjective
  have hf : (generalizedFitting F).map F.subtype = pCore 2 H := by
    rw [fitting_preimage_fitting h,pCore_subnormal_eq_comap 2
      (inferInstance : F.Normal).isSubnormal]
    exact map_comap_eq_self (by rw [range_subtype]; exact twoCore_le_twoFittingCore)
  obtain ⟨n,hn,B,hB,hprod⟩ := Section02Source.fitting_ordered_product h.sqtk
    (R.subgroupOf H) (M.subgroupOf H) h.isRadical h.characteristic_control hf
  have hall (i : Fin n) : B i ≤ M.subgroupOf H := by
    have hi := hB i
    have ha := RankOne.Solvable.isAlternatingBlock_of_equiv
      (subgroupOfEquivOfLe hi.1).symm hi.2.2.2
    have hb : IsChiBlockIn ((B i).subgroupOf F) :=
      ⟨⟨inferInstance,ha.2.1,hi.2.2.1.subnormal.subgroupOf⟩,
        .inr ⟨3,by decide,ha⟩⟩
    have hr : primeRank 3 F ≤ 2 :=
      (Theory.GroupTheory.primeRank_le_of_injective 3 F.subtype F.subtype_injective).trans
        (h.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
    have hnA := SourceShortAction.perfect_normalizes_chi F A (fitting_preimage_fitting h) hr _ hb
    rw [map_subgroupOf_eq_of_le hi.1] at hnA
    have hc := a3_centralized (B i) A hi.2.2.2 hnA
    have hcent := commutator_eq_bot_iff_le_centralizer.mp hc
    intro b hb
    apply h.module_normalizer
    refine ⟨b.property,Subgroup.centralizer_le_normalizer _ ?_⟩
    intro v hv
    have hVH := h.module_le.trans hAH
    exact congrArg Subtype.val (hcent hb ⟨v,hVH hv⟩ (h.module_le hv))
  have hz : n = 0 := by
    by_contra hn0
    let i : Fin n := ⟨0,Nat.pos_of_ne_zero hn0⟩
    exact (hB i).2.1 (hall i)
  subst n
  intro x hx
  obtain ⟨m,hm,l,hl,rfl⟩ := (hprod x).mp hx
  simpa using hm.1
end CFSG.Quasithin.ChapterC.HypothesisC28
