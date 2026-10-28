module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Rank-one detection in the actual central quotient

Two distinct involutions satisfying the rank-one braid generate the familiar
symmetric rank-one configuration. If the first image were central modulo the
ambient center, the braid would force their images equal; centrality of their
product then forces the original involutions equal. Thus the first element
remains noncentral in the actual quotient. This is used at the fixed simple
nodes of twisted E6, where both signed curves belong to the defining-
characteristic subgroup.

Source: the rank-one root relations in GLS3 §1.12, applied to the central-
quotient convention in GLS3 §2.2.
-/

public section
namespace Theory.SpecificGroups.LieType.SourceLevi.RankOne
open Subgroup
variable {H : Type*} [Group H] {x y : H}
private theorem eq_of_commute_of_braid (h : Commute x y)
    (hx : x * x = 1) (hy : y * y = 1)
    (hb : x * y * x = y * x * y) : x = y := by
  have hL : x * y * x = y := by rw [h.eq, mul_assoc, hx, mul_one]
  have hR : y * x * y = x := by rw [← h.eq, mul_assoc, hy, mul_one]
  exact (hL.symm.trans (hb.trans hR)).symm

/-- A nondegenerate rank-one involution pair stays noncentral after quotienting
by the ambient group's center. -/
theorem image_not_mem_center (hx : x * x = 1) (hy : y * y = 1)
    (hb : x * y * x = y * x * y) (hne : x ≠ y) :
    QuotientGroup.mk' (center H) x ∉ center (H ⧸ center H) := by
  intro hc
  let q := QuotientGroup.mk' (center H)
  have hcomm : Commute (q x) (q y) := (mem_center_iff.mp hc (q y)).symm
  have heq : q x = q y := eq_of_commute_of_braid hcomm
    (by rw [← map_mul, hx, map_one]) (by rw [← map_mul, hy, map_one])
    (by simpa only [map_mul] using congrArg q hb)
  have hc' : y * x ∈ center H := (QuotientGroup.eq_one_iff (y * x)).mp (show q (y * x) = 1 by
    rw [map_mul, ← heq, ← map_mul, hx, map_one])
  have hconj : y * x * y = x := by
    calc
      y * x * y = y * (y * x) := (mem_center_iff.mp hc' y).symm
      _ = x := by rw [← mul_assoc, hy, one_mul]
  have he : x * y * x = x := hb.trans hconj
  have hyx : y * x = 1 := mul_left_cancel
    (show x * (y * x) = x * 1 by simpa only [mul_assoc, mul_one] using he)
  apply hne
  symm
  calc
    y = y * (x * x) := by rw [hx, mul_one]
    _ = (y * x) * x := (mul_assoc _ _ _).symm
    _ = x := by rw [hyx, one_mul]

/-- The same marked root element survives the actual central quotient. -/
theorem image_ne_one (hx : x * x = 1) (hy : y * y = 1)
    (hb : x * y * x = y * x * y) (hne : x ≠ y) :
    QuotientGroup.mk' (center H) x ≠ 1 := by
  intro h
  exact image_not_mem_center hx hy hb hne (h ▸ (center _).one_mem)

end Theory.SpecificGroups.LieType.SourceLevi.RankOne
