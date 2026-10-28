module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.IntervalCases

/-!
# Fusion control in a central-involution product

Suppose L has a single class of involutions and w is a central involution
of C. Inside the join of L and ⟨w⟩, an involution lies either in L or in
the opposite coset. If w and wz fuse in the ambient group, while z and w
do not, an ambient conjugate of z in this join must be conjugate to z in C.
Conjugation into a prescribed Sylow subgroup and outside nonfusion extend
this conclusion to every ambient conjugate of z in C.

The local premises are explicit; no ambient simplicity or recognition is
assumed. Source: Aschbacher--Smith 14.3.22, printed p.999.
-/

public section

open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem conj_order {E : Type*} [Group E] {x y : E} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private theorem two_zpowers_cases {E : Type*} [Group E] [Finite E]
    {w x : E} (hw : orderOf w = 2) (hx : x ∈ zpowers w) : x = 1 ∨ x = w := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hw] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

private theorem involution_conjugate_into_sylow {E : Type*} [Group E] [Finite E]
    (S : Sylow 2 E) (a : E) (ha : orderOf a = 2) :
    ∃ y : S, IsConj a (y : E) := by
  have hp : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using ha)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E P S
  have hy : (MulAut.conj g) a ∈ S := by
    rw [← hg]
    change (MulAut.conj g) • a ∈ (MulAut.conj g) • (P : Set E)
    exact Set.smul_mem_smul_set (hP (mem_zpowers a))
  exact ⟨⟨(MulAut.conj g) a, hy⟩, isConj_iff.mpr ⟨g, rfl⟩⟩

/-- In a central involution product, the opposite coset consists of the
central involution and its products with the one involution class of L. -/
theorem isConj_of_mem_central_involution_join
    (C : Subgroup G) (L : Subgroup C) [L.Normal] (w z : C)
    (hw : orderOf w = 2) (hwc : w ∈ center C) (hz : orderOf z = 2) (hzL : z ∈ L)
    (hclass : ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hnon : ¬ IsConj (z : G) (w : G))
    (hopp : IsConj (w : G) ((w * z : C) : G))
    (a : C) (haJ : a ∈ zpowers w ⊔ L) (hza : IsConj (z : G) (a : G)) :
    IsConj z a := by
  have ha : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (conj_order hza).symm.trans ((Subgroup.orderOf_coe z).trans hz)
  obtain ⟨k, hk, l, hl, rfl⟩ := mem_sup_of_normal_right.mp haJ
  have class_to (x : C) (hx : x ∈ L) (ho : orderOf x = 2) : IsConj z x := by
    exact L.subtype.map_isConj (hclass ⟨z, hzL⟩ ⟨x, hx⟩
      ((Subgroup.orderOf_coe _).symm.trans hz) ((Subgroup.orderOf_coe _).symm.trans ho))
  rcases two_zpowers_cases hw hk with hk1 | hkw
  · subst k
    simpa only [one_mul] using class_to l hl (by simpa only [one_mul] using ha)
  · subst k
    have hlsq : l ^ 2 = 1 := by
      have hc : Commute w l := (mem_center_iff.mp hwc l).symm
      have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
      have ha2 : (w * l) ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one _
      simpa only [hc.mul_pow, hw2, one_mul] using ha2
    have hwy : IsConj (w : G) ((w * l : C) : G) := by
      by_cases hl1 : l = 1
      · simpa only [hl1, mul_one] using (IsConj.refl (w : G))
      · have hzl := class_to l hl (orderOf_eq_prime hlsq hl1)
        obtain ⟨c, hc⟩ := isConj_iff.mp hzl
        have he : c * (w * z) * c⁻¹ = w * l := by
          calc
            c * (w * z) * c⁻¹ = w * (c * z * c⁻¹) := by
              rw [← mul_assoc c w z, mem_center_iff.mp hwc c]
              simp only [mul_assoc]
            _ = w * l := by rw [hc]
        exact hopp.trans (C.subtype.map_isConj (isConj_iff.mpr ⟨c, he⟩))
    exact (hnon (hza.trans hwy.symm)).elim

/-- Localize an ambient conjugate in a chosen Sylow subgroup, use outside
nonfusion to enter B, then exclude the opposite central-involution coset. -/
theorem fusion_control_of_central_involution_join
    (C : Subgroup G) (L : Subgroup C) [L.Normal] (w z : C)
    (hw : orderOf w = 2) (hwc : w ∈ center C) (hz : orderOf z = 2) (hzL : z ∈ L)
    (hclass : ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hnon : ¬ IsConj (z : G) (w : G))
    (hopp : IsConj (w : G) ((w * z : C) : G))
    (S : Sylow 2 C) (T B : Subgroup G)
    (hST : (S : Subgroup C).map C.subtype ≤ T)
    (hB : (S : Subgroup C).map C.subtype ⊓ B ≤ (zpowers w ⊔ L).map C.subtype)
    (hout : ∀ t ∈ T, orderOf t = 2 → t ∉ B → ¬ IsConj (z : G) t)
    (a : C) (hza : IsConj (z : G) (a : G)) : IsConj z a := by
  have ha : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (conj_order hza).symm.trans ((Subgroup.orderOf_coe z).trans hz)
  obtain ⟨y, hay⟩ := involution_conjugate_into_sylow S a ha
  have hzy : IsConj (z : G) ((y : C) : G) := hza.trans (C.subtype.map_isConj hay)
  have hyS : ((y : C) : G) ∈ (S : Subgroup C).map C.subtype :=
    mem_map_of_mem C.subtype y.property
  have hyB : ((y : C) : G) ∈ B := by
    by_contra hyB
    exact hout _ (hST hyS)
      ((conj_order hzy).symm.trans ((Subgroup.orderOf_coe z).trans hz)) hyB hzy
  have hyJ : (y : C) ∈ zpowers w ⊔ L := by
    obtain ⟨x, hx, he⟩ := hB ⟨hyS, hyB⟩
    exact (C.subtype_injective he) ▸ hx
  exact (isConj_of_mem_central_involution_join C L w z hw hwc hz hzL
    hclass hnon hopp y hyJ hzy).trans hay.symm
end Subgroup
