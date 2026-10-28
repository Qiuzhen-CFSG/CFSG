module

public import Theory.Mathieu.M22.CentralCoverPrelude

/-!
# Squares in central double covers of M₂₂

Every lift of a square-one element has square one. Quotient involutions have
involutory lifts, and multiplying a chosen lift by the central kernel of
order two preserves its square. This supplies commuting lifts of a Klein
four pair in the binary hexad splitting argument.

Source: Aschbacher–Smith I.2.2(ii) and (6), printed pp.410 and 412.
-/

public section
namespace Sporadic.Mathieu.M22CentralCover
open Subgroup
variable {K : Type*} [Group K] [Finite K]

/-- In a central double cover every lift of a square-one element has square one. -/
theorem square_eq_one (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 2) (x : K) (hx : (projection e x) ^ 2 = 1) :
    x ^ 2 = 1 := by
  have hk (z : K) (hz : projection e z = 1) : z ^ 2 = 1 := by
    have hc : z ∈ center K := projection_ker e ▸ hz
    have hp := pow_card_eq_one' (x := (⟨z, hc⟩ : center K))
    rw [hZ] at hp
    exact congrArg Subtype.val hp
  by_cases hn : projection e x = 1
  · exact hk x hn
  obtain ⟨y, hy, hyo⟩ := involutions_lift e hZ _
    (orderOf_eq_prime_iff.mpr ⟨hx, hn⟩)
  have hd : projection e (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hy, mul_inv_cancel]
  have hc : Commute (x * y⁻¹) y :=
    (mem_center_iff.mp (projection_ker e ▸ hd) y).symm
  have hp := hc.mul_pow 2
  rw [inv_mul_cancel_right, hk _ hd,
    show y ^ 2 = 1 from hyo ▸ pow_orderOf_eq_one y, mul_one] at hp
  exact hp

end Sporadic.Mathieu.M22CentralCover
