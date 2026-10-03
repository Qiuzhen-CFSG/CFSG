module

public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.IndexNormal

/-!
# Action on cyclic rotations of index two

If a group has cyclic rotations of index two and its center has exponent two,
an outside element inverts every rotation of order four and fixes exactly two
rotations. Indeed, a rotation commuting with an outside element is central.
The order-four action then follows from uniqueness of the cyclic involution.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.392, Case 1.
The centrality argument adapts `LargeHallRotationStructure`.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

public theorem central_of_commute_outside_cyclic_index_two {G : Type*} [Group G]
    (R : Subgroup G) [IsCyclic R] (hi : R.index = 2)
    {d z : G} (hd : d ∉ R) (hz : z ∈ R) (hc : Commute z d) :
    z ∈ center G := by
  apply mem_center_iff.mpr
  intro x
  by_cases hx : x ∈ R
  · exact R.le_centralizer hz x hx
  · have hy : x * d⁻¹ ∈ R := (R.mul_mem_iff_of_index_two hi).mpr (by simpa using iff_of_false hx hd)
    have hh : Commute z (x * d⁻¹) := R.le_centralizer hy z hz
    have he := hh.mul_right hc
    simpa using he.symm.eq

private theorem cyclic_order_four_eq_or_inv {G : Type*} [Group G] [Finite G]
    [IsCyclic G] {x y : G} (hx : orderOf x = 4) (hy : orderOf y = 4) :
    y = x ∨ y = x⁻¹ := by
  have hx2 : orderOf (x ^ 2) = 2 := by rw [orderOf_pow, hx]; decide
  have hy2 : orderOf (y ^ 2) = 2 := by rw [orderOf_pow, hy]; decide
  have he : y ^ 2 = x ^ 2 := IsCyclic.eq_of_orderOf_eq_two hy2 hx2
  have hc : Commute y x⁻¹ := (Commute.all y x⁻¹)
  have hs : (y * x⁻¹) ^ 2 = 1 := by rw [hc.mul_pow, inv_pow, he, mul_inv_cancel]
  by_cases h : y * x⁻¹ = 1
  · exact Or.inl (mul_inv_eq_one.mp h)
  · have ho : orderOf (y * x⁻¹) = 2 := orderOf_eq_prime hs h
    have hh : y * x⁻¹ = x ^ 2 := IsCyclic.eq_of_orderOf_eq_two ho hx2
    right
    have h4 : x ^ 4 = 1 := hx ▸ pow_orderOf_eq_one x
    calc
      y = x ^ 2 * x := (mul_inv_eq_iff_eq_mul.mp hh)
      _ = x⁻¹ := by
        apply mul_right_cancel (b := x)
        simpa only [pow_succ, pow_zero, one_mul, inv_mul_cancel] using h4

/-- An outside element inverts every order-four rotation when the center has exponent two. -/
public theorem conj_eq_inv_of_outside_cyclic_index_two {G : Type*} [Group G] [Finite G]
    (R : Subgroup G) [IsCyclic R] (hi : R.index = 2)
    (hZ : ∀ z ∈ center G, z ^ 2 = (1 : G))
    {d w : G} (hd : d ∉ R) (hwR : w ∈ R) (hw : orderOf w = 4) :
    d * w * d⁻¹ = w⁻¹ := by
  let : R.Normal := normal_of_index_eq_two hi
  have hyR : d * w * d⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem w hwR d
  have hy : orderOf (d * w * d⁻¹) = 4 := (MulAut.conj d).orderOf_eq w |>.trans hw
  rcases cyclic_order_four_eq_or_inv
      (x := (⟨w, hwR⟩ : R)) (y := ⟨d * w * d⁻¹, hyR⟩)
      (by rwa [← orderOf_coe]) (by rwa [← orderOf_coe]) with h | h
  · have he : d * w * d⁻¹ = w := congrArg Subtype.val h
    have hc : Commute w d := (mul_inv_eq_iff_eq_mul.mp he).symm
    have hs := hZ w (central_of_commute_outside_cyclic_index_two R hi hd hwR hc)
    have hh := orderOf_dvd_of_pow_eq_one hs
    rw [hw] at hh
    norm_num at hh
  · exact congrArg Subtype.val h

/-- Exactly two rotations commute with an outside element. -/
public theorem card_inf_centralizer_of_outside_cyclic_index_two {G : Type*} [Group G] [Finite G]
    (R : Subgroup G) [IsCyclic R] (hi : R.index = 2)
    (hZ : ∀ z ∈ center G, z ^ 2 = (1 : G))
    {d w : G} (hd : d ∉ R) (hwR : w ∈ R) (hw : orderOf w = 4) :
    Nat.card (R ⊓ centralizer ({d} : Set G) : Subgroup G) = 2 := by
  let I := R ⊓ centralizer ({d} : Set G)
  let : IsCyclic I := isCyclic_of_le (show I ≤ R from inf_le_left)
  have hle : Nat.card I ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0 < 2)
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    exact hZ x (central_of_commute_outside_cyclic_index_two R hi hd x.property.1
      (mem_centralizer_singleton_iff.mp x.property.2))
  have hwi := conj_eq_inv_of_outside_cyclic_index_two R hi hZ hd hwR hw
  have hw4 : w ^ 4 = 1 := hw ▸ pow_orderOf_eq_one w
  have hw2 : w⁻¹ ^ 2 = w ^ 2 := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_add] using hw4
  have hc : Commute (w ^ 2) d := by
    have h := congrArg (fun g : G => g ^ 2) hwi
    have he : d * w ^ 2 * d⁻¹ = w ^ 2 := by
      change (MulAut.conj d w) ^ 2 = _ at h
      rw [← map_pow] at h
      exact h.trans hw2
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hm : w ^ 2 ∈ I := ⟨R.pow_mem hwR 2, mem_centralizer_singleton_iff.mpr hc⟩
  have hlo : Nat.card (zpowers (w ^ 2)) ≤ Nat.card I := card_le_of_le (zpowers_le.mpr hm)
  rw [Nat.card_zpowers, orderOf_pow, hw] at hlo
  norm_num at hlo
  change Nat.card I = 2
  omega
end Subgroup
