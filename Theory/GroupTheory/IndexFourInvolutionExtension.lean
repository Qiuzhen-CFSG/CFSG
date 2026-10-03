module

public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Adjoining an involution to a subgroup of index four

An outside normalizing involution doubles the order of a subgroup of index
four, giving a subgroup of index two. If the first subgroup lies in another
subgroup that omits the involution, the intersection with that subgroup is
exactly the first subgroup.

These elementary counting and coset facts are used in Janko–Thompson,
Math. Z. 113 (1970), §4, printed p.392, to construct the maximal subgroup
from the characteristic rotation product.
-/

namespace Subgroup

/-- Adjoining an outside normalizing involution halves index four. -/
public theorem index_sup_zpowers_eq_two_of_index_four
    {P : Type*} [Group P] [Finite P]
    (K : Subgroup P) (hK : K.index = 4) (t : P)
    (ht : t ^ 2 = 1) (hout : t ∉ K) (hnorm : t ∈ normalizer K) :
    (K ⊔ zpowers t).index = 2 := by
  have hcard := card_sup_zpowers_of_normalizing_involution K t ht hout hnorm
  have hfirst := K.index_mul_card
  have hsecond := (K ⊔ zpowers t).index_mul_card
  rw [hK] at hfirst
  rw [hcard] at hsecond
  have hpos := Nat.card_pos (α := K)
  nlinarith

/-- The new involution coset cannot meet an overgroup omitting that involution. -/
public theorem inf_sup_zpowers_eq_of_involution_notMem
    {P : Type*} [Group P]
    (K H : Subgroup P) [K.Normal] (hKH : K ≤ H)
    (t : P) (ht : orderOf t = 2) (hout : t ∉ H) :
    H ⊓ (K ⊔ zpowers t) = K := by
  classical
  apply le_antisymm ?_ (le_inf hKH le_sup_left)
  intro u hu
  obtain ⟨k, hk, v, hv, rfl⟩ := mem_sup_of_normal_left.mp hu.2
  have hfin : IsOfFinOrder t := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2, by decide, by simpa only [ht] using pow_orderOf_eq_one t⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, ht] at hv
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
  have hn2 := Finset.mem_range.mp hn
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · simpa using hk
  · have hkt : k * t ∈ H := by simpa using hu.1
    exact (hout (by simpa using H.mul_mem (H.inv_mem (hKH hk)) hkt)).elim

end Subgroup
