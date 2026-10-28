module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore

/-!
# Restricting an odd-index radical to a subnormal supplement

Let K be subnormal in a finite group, and suppose R = O₂(P) normalizes K.
The intersection P ∩ KR is subnormal in P: modulo R it is the image of
P ∩ K. Consequently its two-core is exactly R. If P has odd index, its
Sylow two-subgroup meets K in a Sylow subgroup, and the normal-product
index formula shows that P ∩ KR has odd index in KR.

This is the source-preserving restriction of MS2(a) used in the A₆ branch
of Aschbacher--Smith C.2.7, pp.146--147, when the original application
already supplies an odd-index radical witness.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem restricted_subnormal (K P : Subgroup G) (hK : K.IsSubnormal)
    (hn : P.pCoreIn 2 ≤ normalizer K) :
    ((K ⊔ P.pCoreIn 2).subgroupOf P).IsSubnormal := by
  have hs := (hK.subgroupOf (K := P)).map (QuotientGroup.mk'_surjective (pCore 2 P))
  have hc := hs.comap (QuotientGroup.mk' (pCore 2 P))
  rw [comap_map_eq, QuotientGroup.ker_mk'] at hc
  convert hc using 1
  let J := K ⊔ P.pCoreIn 2
  ext x
  constructor
  · intro hx
    have hx' : (x : G) ∈ (K : Set G) * (P.pCoreIn 2 : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left K (P.pCoreIn 2) hn]
      exact hx
    obtain ⟨k,hk,r,hr,hkr⟩ := hx'
    have hrP : r ∈ P := P.pCoreIn_le 2 hr
    have hkP : k ∈ P := by
      have hh := P.mul_mem x.property (P.inv_mem hrP)
      rw [← hkr,mul_inv_cancel_right] at hh
      exact hh
    have hr' : (⟨r,hrP⟩ : P) ∈ pCore 2 P := by
      obtain ⟨a,ha,he⟩ := hr
      exact (Subtype.ext he : a = ⟨r,hrP⟩) ▸ ha
    have he : (⟨k,hkP⟩ : P) * ⟨r,hrP⟩ = x := Subtype.ext hkr
    rw [←he]
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr')
  · intro hx
    obtain ⟨k,hk,r,hr,rfl⟩ := mem_sup_of_normal_right.mp hx
    exact mul_mem (mem_sup_left hk) (mem_sup_right (mem_map_of_mem P.subtype hr))

theorem pCoreIn_subnormal_core_supplement (K P : Subgroup G) (hK : K.IsSubnormal)
    (hn : P.pCoreIn 2 ≤ normalizer K) :
    (P.subgroupOf (K ⊔ P.pCoreIn 2)).pCoreIn 2 =
      (P.pCoreIn 2).subgroupOf (K ⊔ P.pCoreIn 2) := by
  let J := K ⊔ P.pCoreIn 2
  have hu := map_mono (f := P.subtype)
    (pCoreIn_le_of_subnormal 2 (restricted_subnormal K P hK hn))
  rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,subgroupOf_map_subtype,inf_comm] at hu
  have hl : P.pCoreIn 2 ≤ (P ⊓ J).pCoreIn 2 :=
    (le_inf (le_inf (P.pCoreIn_le 2) le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (show P ⊓ J ≤ P from inf_le_left))
  have he : (P ⊓ J).pCoreIn 2 = P.pCoreIn 2 := le_antisymm hu hl
  apply map_injective J.subtype_injective
  rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,subgroupOf_map_subtype,
    map_subgroupOf_eq_of_le (show P.pCoreIn 2 ≤ J from le_sup_right)]
  exact he

theorem odd_index_subnormal_core_supplement (K P : Subgroup G) (hK : K.IsSubnormal)
    (hn : P.pCoreIn 2 ≤ normalizer K) (ho : Odd P.index) :
    Odd (P.subgroupOf (K ⊔ P.pCoreIn 2)).index := by
  let Q : Sylow 2 P := Classical.choice inferInstance
  let S0 := (Q : Subgroup P).map P.subtype
  have hs0 : ¬ 2 ∣ S0.index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul (by decide) Q.not_dvd_index ho.not_two_dvd_nat
  let S : Sylow 2 G := (Q.isPGroup'.map P.subtype).toSylow hs0
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_subnormal K hK
  have hPK : Odd (P.subgroupOf K).index := by
    rw [← Nat.not_even_iff_odd,even_iff_two_dvd]
    intro hd
    apply T.not_dvd_index
    apply hd.trans
    apply index_dvd_of_le
    rw [hT]
    intro x hx
    exact map_subtype_le (Q : Subgroup P) hx
  let J := K ⊔ P.pCoreIn 2
  let K0 := K.subgroupOf J
  let P0 := P.subgroupOf J
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hgen : K0 ⊔ P0 = ⊤ := by
    apply top_unique
    have hr : (P.pCoreIn 2).subgroupOf J ≤ P0 := comap_mono (P.pCoreIn_le 2)
    calc
      ⊤ = K0 ⊔ (P.pCoreIn 2).subgroupOf J := by
        rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
      _ ≤ K0 ⊔ P0 := sup_le_sup_left hr _
  have hi : P0.index = (P.subgroupOf K).index := by
    calc
      P0.index = P0.relIndex (K0 ⊔ P0) := by rw [hgen,relIndex_top_right]
      _ = P0.relIndex K0 := relIndex_sup_of_normal_left K0 P0
      _ = P.relIndex K := relIndex_subgroupOf le_sup_left
  exact hi.symm ▸ hPK
end Subgroup
