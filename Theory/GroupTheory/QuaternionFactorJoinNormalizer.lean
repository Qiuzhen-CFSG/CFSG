module
public import Theory.GroupTheory.QuaternionCentralProductC2Rank
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-! The literal elementary sixteen is characteristic in AU if all outside
involutions belong to A. An elementary sixteen has an element outside the
quaternion core; multiplying by it detects membership of every element.
Source:14.3.18(6). -/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]

theorem normalizer_join_le_of_outside_involutions
    (U A:Subgroup G) (d:QuaternionCentralProductData U)
    [IsElementaryAbelian 2 A] (hA:Nat.card A=16)
    (hinv:∀x∈A⊔U,x∉U→x^2=1→x∈A) :
    normalizer ((A⊔U:Subgroup G):Set G)≤normalizer (A:Set G) := by
  have hlarge (E:Subgroup G) [IsElementaryAbelian 2 E]
      (hc:Nat.card E=16) (hE:E≤A⊔U) : E=A := by
    have hout:∃x∈E,x∉U := by
      by_contra! hh
      have he:IsElementaryAbelian 2 (E.subgroupOf U) := IsElementaryAbelian.subgroupOf hh
      have hb:=d.elementary_card_le_eight (E.subgroupOf U) he
      rw [Nat.card_congr (subgroupOfEquivOfLe hh).toEquiv,hc] at hb
      omega
    obtain ⟨x,hx,hxu⟩:=hout
    have hxA:=hinv x (hE hx) hxu (elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx)
    apply eq_of_le_of_card_ge ?_ (by rw [hc,hA])
    intro y hy
    by_cases hyu:y∈U
    · have hxyu:x*y∉U := by
        intro hh
        apply hxu
        simpa only [mul_inv_cancel_right] using U.mul_mem hh (U.inv_mem hyu)
      have hxyA:=hinv (x*y) (hE (E.mul_mem hx hy)) hxyu
        (elemPow_eq_one_of_isElementaryAbelian (p:=2) (x*y) (E.mul_mem hx hy))
      simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem hxA) hxyA
    · exact hinv y (hE hy) hyu (elemPow_eq_one_of_isElementaryAbelian (p:=2) y hy)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  let e:=MulAut.conj g
  let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
  change A.map e.toMonoidHom=A
  apply hlarge (A.map e.toMonoidHom)
  · exact (card_map_of_injective e.injective).trans hA
  · have hh:=map_mono (f:=e.toMonoidHom) (le_sup_left: A≤A⊔U)
    have he:(A⊔U).map e.toMonoidHom=A⊔U := (mem_normalizer_iff_map_conj_eq.mp hg)
    exact hh.trans he.le
end Subgroup
