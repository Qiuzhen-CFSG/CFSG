module

public import Theory.GroupTheory.IndexFourInvolutionExtension
public import Theory.GroupTheory.IndexFourCosetFusion
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Involution transfer across a normal subgroup of index four

If the involutions in an outside coset form one orbit under the normal
subgroup, its involution centralizer covers the quotient. Adjoining that
involution gives an index-two subgroup, so Thompson transfer extends a
class cover of the core and this coset to the whole Sylow subgroup.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (b)(ii), p.391.
-/

namespace Subgroup

/-- Transitivity under the core on the involutions in one coset forces the
centralizer of its representative to cover the quotient of order four. -/
public theorem sup_centralizer_eq_top_of_index_four_coset_involutions
    {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] (hindex : H.index = 4)
    (t : P) (ht : orderOf t = 2)
    (hcoset : ∀ u : P, orderOf u = 2 → u * t⁻¹ ∈ H →
      ∃ h : P, h ∈ H ∧ h * t * h⁻¹ = u) :
    H ⊔ centralizer ({t} : Set P) = ⊤ := by
  apply top_unique
  intro g _
  have hu : orderOf (g * t * g⁻¹) = 2 :=
    ((MulAut.conj g).orderOf_eq t).trans ht
  obtain ⟨h, hh, heq⟩ := hcoset (g * t * g⁻¹) hu
    (conjugate_mul_inv_mem_of_index_four H hindex g t)
  have hc : h⁻¹ * g ∈ centralizer ({t} : Set P) := by
    apply mem_centralizer_singleton_iff.mpr
    have heq' := congrArg (fun x => h⁻¹ * x * g) heq
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using heq'.symm
  have hm := (H ⊔ centralizer ({t} : Set P)).mul_mem
    (mem_sup_left hh) (mem_sup_right hc)
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hm

/-- Once the centralizer covers the quotient, its order is four times the
fixed-core order. -/
public theorem card_centralizer_of_index_four_coset_involutions
    {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] (hindex : H.index = 4)
    (t : P) (ht : orderOf t = 2)
    (hcoset : ∀ u : P, orderOf u = 2 → u * t⁻¹ ∈ H →
      ∃ h : P, h ∈ H ∧ h * t * h⁻¹ = u) :
    Nat.card (centralizer ({t} : Set P)) =
      Nat.card (H.subgroupOf (centralizer ({t} : Set P))) * 4 := by
  have hcover := sup_centralizer_eq_top_of_index_four_coset_involutions H hindex t ht hcoset
  have hi : (H.subgroupOf (centralizer ({t} : Set P))).index = 4 := by
    change H.relIndex (centralizer ({t} : Set P)) = 4
    rw [← relIndex_sup_left, hcover, relIndex_top_right, hindex]
  have hc := (H.subgroupOf (centralizer ({t} : Set P))).card_mul_index
  rw [hi] at hc
  exact hc.symm

end Subgroup

namespace Sylow
open Subgroup

/-- A core class cover and a single outside involution class give a class
cover of the whole Sylow group by Thompson transfer. -/
public theorem involution_cover_of_index_four_coset
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (H W : Subgroup S) [H.Normal] (hindex : H.index = 4)
    (z t : S) (hzW : z ∈ W) (ht : orderOf t = 2) (hout : t ∉ H)
    (hzt : IsConj (z : G) (t : G))
    (hinside : ∀ u : S, u ∈ H → orderOf u = 2 →
      ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G))
    (hcoset : ∀ u : S, orderOf u = 2 → u * t⁻¹ ∈ H → IsConj (t : G) (u : G)) :
    ∀ u : S, orderOf u = 2 → ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G) := by
  classical
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have hM := index_sup_zpowers_eq_two_of_index_four H hindex t ht2 hout
    (by rw [H.normalizer_eq_top]; trivial)
  intro u hu
  obtain ⟨v, huv, hvM⟩ := S.exists_isConj_mem_of_index_two hno _ hM u hu
  have hv : orderOf v = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp huv
    have he : (MulAut.conj g) (u : G) = v := hg
    rw [← orderOf_coe, ← he, MulEquiv.orderOf_eq, orderOf_coe, hu]
  by_cases hvH : v ∈ H
  · obtain ⟨w, hw, hvw⟩ := hinside v hvH hv
    exact ⟨w, hw, huv.trans hvw⟩
  · have hcos : v * t⁻¹ ∈ H := by
      obtain ⟨k, hk, a, ha, rfl⟩ := mem_sup_of_normal_left.mp hvM
      rw [mem_zpowers_iff_mem_range_orderOf, ht] at ha
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
      have hn2 := Finset.mem_range.mp hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · exact (hvH (by simpa using hk)).elim
      · simpa using hk
    exact ⟨z, hzW, huv.trans ((hcoset v hv hcos).symm.trans hzt.symm)⟩

end Sylow
