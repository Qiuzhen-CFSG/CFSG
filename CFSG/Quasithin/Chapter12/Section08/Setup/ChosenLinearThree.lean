module
public import CFSG.Quasithin.Chapter12.Section08.Setup.NaturalActions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.Representation.PSL3Two.SmallModules

/-!
# The whole local join of a chosen binary three-space

A chosen natural SL₃(2)-module admits every linear automorphism from its
component K. The action kernel in H=KT is a two-group: its intersection
with K lies in O₂(K), and H/K is a two-group. Conversely the reduced
module is centralized by O₂(H). Full action then gives H=K O₂(H), and
restriction of H→H/O₂(H) identifies that quotient with K/O₂(K).

The theorem requires only the literal chosen module and its coordinates;
it uses no higher-rank ambient setup or additional model exclusions.
The original augmentation consumer is ComponentLinearWhole.
Source: Aschbacher–Smith 13.4.10(4), printed pp.907–909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {K U : Subgroup G}

/-- A chosen natural three-space makes the component supplement the whole
local two-core and identifies both its action kernel and quotient. -/
theorem chosen_linear_three_join
    (DK : ChosenModule T K U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (q : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : U ≃* Multiplicative BinaryLinearThree.Vector)
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
        BinaryLinearThree.W (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    let H := K ⊔ (T : Subgroup G)
    H ⊓ centralizer (U : Set G) = H.pCoreIn 2 ∧
      K ⊔ H.pCoreIn 2 = H ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* BinaryLinearThree.Group) := by
  let H := K ⊔ (T : Subgroup G)
  let := DK.elementary
  let ca := e.toAdditive.trans (AddEquiv.additiveMultiplicative (G := BinaryLinearThree.Vector))
  let c : Additive U ≃ₗ[ZMod 2] BinaryLinearThree.Vector :=
    { ca with map_smul' := ZMod.map_smul ca }
  let a : InvariantFlag.AmbientNaturalMarking K DK.normalizes 3 :=
    ⟨q.trans (BinaryLinear.OuterCyclic.slEquivLinear 3),c,fun k v => he k v.toMul⟩
  have hKC := a.centralizer_eq_core
  have hHU := sup_le DK.normalizes hTU
  let N := K.subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer DK.sylow_normalizes_component)
  have hgen : N ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (H ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    ((T : Subgroup G).subgroupOf H) T.isPGroup'.comap_subtype hgen
  let f := setupSeedAction H U hHU
  let r := (QuotientGroup.mk' N).comp f.ker.subtype
  have hr : IsPGroup 2 r.ker := by
    let s : r.ker →* K :=
      (H.subtype.comp (f.ker.subtype.comp r.ker.subtype)).codRestrict K (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hs : ∀ x : r.ker, s x ∈ pCore 2 K := by
      intro x
      have hc : (x.val.val : G) ∈ centralizer (U : Set G) :=
        (setupSeedAction_ker H U hHU).le x.val.property
      have hx : (s x : G) ∈ K.pCoreIn 2 := hKC ▸ ⟨(s x).property,hc⟩
      obtain ⟨y,hy,heq⟩ := hx
      exact (Subtype.ext heq : y = s x) ▸ hy
    let s' : r.ker →* pCore 2 K := s.codRestrict _ hs
    apply pCore_isPGroup.of_injective s'
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 K => (x.val : G)) hxy
  have hk : IsPGroup 2 f.ker := by
    have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup r hr
    rw [comap_top] at hh
    exact hh.of_equiv topEquiv
  have hC : H ⊓ centralizer (U : Set G) = H.pCoreIn 2 := by
    apply le_antisymm
    · have hh := map_mono (f := H.subtype)
        (show f.ker ≤ pCore 2 H from le_sSup ⟨inferInstance,hk⟩)
      rwa [setupSeedAction_ker,subgroupOf_map_subtype,inf_comm] at hh
    · exact le_inf (pCoreIn_le 2 H) DK.core_centralizes
  have hsup : K ⊔ H.pCoreIn 2 = H := by
    apply le_antisymm (sup_le le_sup_left (pCoreIn_le 2 H))
    intro x hx
    obtain ⟨k,hk,heq⟩ := a.full_action (f ⟨x,hx⟩)
    have hsame : f ⟨k,mem_sup_left hk⟩ = f ⟨x,hx⟩ := by
      ext v
      exact heq v
    have hcx : k⁻¹ * x ∈ H.pCoreIn 2 := by
      rw [←hC]
      refine ⟨H.mul_mem (H.inv_mem (mem_sup_left hk)) hx,?_⟩
      have hh : (⟨k,mem_sup_left hk⟩⁻¹ * ⟨x,hx⟩ : H) ∈ f.ker := by
        change f (⟨k,mem_sup_left hk⟩⁻¹ * ⟨x,hx⟩) = 1
        rw [map_mul,map_inv,hsame,inv_mul_cancel]
      exact (setupSeedAction_ker H U hHU).le hh
    have hm := (K ⊔ H.pCoreIn 2).mul_mem (mem_sup_left hk) (mem_sup_right hcx)
    simpa only [mul_inv_cancel_left] using hm
  let j : K →* (H ⧸ pCore 2 H) :=
    (QuotientGroup.mk' (pCore 2 H)).comp (inclusion (show K ≤ H from le_sup_left))
  have hj : Function.Surjective j := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) y
    have hmem : x.val ∈ K ⊔ H.pCoreIn 2 := hsup.symm ▸ x.property
    have hn : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
      by exact comap_map_eq_self_of_injective H.subtype_injective _
    have hmem' : x ∈ N ⊔ pCore 2 H := by
      rw [←hn,←subgroupOf_sup (show K ≤ H from le_sup_left) (pCoreIn_le 2 H)]
      exact hmem
    obtain ⟨k,hk,b,hb,hkb⟩ := mem_sup_of_normal_right.mp hmem'
    refine ⟨⟨k.val,hk⟩,?_⟩
    change QuotientGroup.mk' (pCore 2 H) k = QuotientGroup.mk' (pCore 2 H) x
    have hbq : QuotientGroup.mk' (pCore 2 H) b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
    rw [←hkb,map_mul,hbq,mul_one]
  have hjk : j.ker = pCore 2 K := by
    ext k
    change QuotientGroup.mk' (pCore 2 H) (inclusion le_sup_left k) = 1 ↔ _
    refine (QuotientGroup.eq_one_iff (N := pCore 2 H) (inclusion (show K ≤ H from le_sup_left) k)).trans ?_
    have hkm : (k : G) ∈ H.pCoreIn 2 ↔ k ∈ pCore 2 K := by
      rw [←hC]
      change (k.val ∈ H ∧ k.val ∈ centralizer (U : Set G)) ↔ _
      rw [and_iff_right (mem_sup_left k.property)]
      have hh : k.val ∈ centralizer (U : Set G) ↔ k.val ∈ K.pCoreIn 2 := by
        rw [←hKC]
        exact (and_iff_right k.property).symm
      exact hh.trans (mem_map_iff_mem K.subtype_injective)
    exact (mem_map_iff_mem H.subtype_injective).symm.trans hkm
  exact ⟨hC,hsup,⟨(QuotientGroup.quotientKerEquivOfSurjective j hj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hjk).trans q)⟩⟩

end CFSG.Quasithin.Chapter12.Section08
