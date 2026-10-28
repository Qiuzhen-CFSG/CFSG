module

public import Theory.Mathieu.M22.CentralCoverPrelude

/-!
# Elementary pullbacks in every central double extension of M₂₂

The double-extension involution argument only needs a surjective map with
central kernel of order two. In particular it applies after factoring a
larger center, without first identifying the center of that intermediate
quotient. Native involution fusion propagates one lift supplied by the
hexad E₁₆, and centrality makes both lifts have square one.

Source: Aschbacher–Smith I.2.2(ii) and (6), printed pp.410 and 412.
-/

public section
namespace Sporadic.Mathieu.M22CentralCover
open Subgroup Theory.GroupTheory.DoubleCoverInvolutionLifting
variable {K : Type*} [Group K] [Finite K]

theorem involutions_lift_of_central_double_extension (f : K →* M22)
    (hf : Function.Surjective f) (hk : Nat.card f.ker = 2)
    (u : M22) (hu : orderOf u = 2) :
    ∃ v : K, f v = u ∧ orderOf v = 2 := by
  let E := m22HexadPointwiseKernel m22Hexad123
  let : IsElementaryAbelian 2 E := m22HexadPointwiseKernel_elementaryAbelian m22Hexad123_mem
  obtain ⟨x, hx, _, hxn⟩ := exists_involution_above_elementary_subgroup f hf hk E
    (by rw [m22HexadPointwiseKernel_card m22Hexad123_mem]; decide)
  have hxo : orderOf (f x) = 2 := orderOf_eq_prime
    (by rw [← map_pow, show x ^ 2 = 1 from hx ▸ pow_orderOf_eq_one x, map_one]) hxn
  exact involution_lift_of_isConj f hf hx (m22_involutions_isConj _ u hxo hu)

/-- Centrality makes every lift of every elementary element square to one. -/
theorem square_eq_one_of_central_double_extension (f : K →* M22)
    (hf : Function.Surjective f) (hk : Nat.card f.ker = 2)
    (hcentral : f.ker ≤ center K) (x : K) (hx : (f x) ^ 2 = 1) : x ^ 2 = 1 := by
  have kernel_square {y : K} (hy : f y = 1) : y ^ 2 = 1 := by
    have hp := pow_card_eq_one' (x := (⟨y, hy⟩ : f.ker))
    rw [hk] at hp
    exact congrArg Subtype.val hp
  by_cases h : f x = 1
  · exact kernel_square h
  obtain ⟨y, hy, hyo⟩ := involutions_lift_of_central_double_extension f hf hk _
    (orderOf_eq_prime hx h)
  have hd : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hy, mul_inv_cancel]
  have hc : Commute (x * y⁻¹) y := (mem_center_iff.mp (hcentral hd) y).symm
  have hp := hc.mul_pow 2
  rw [inv_mul_cancel_right, kernel_square hd,
    show y ^ 2 = 1 from hyo ▸ pow_orderOf_eq_one y, mul_one] at hp
  exact hp

theorem elementary_preimage_of_central_double_extension (f : K →* M22)
    (hf : Function.Surjective f) (hk : Nat.card f.ker = 2)
    (hcentral : f.ker ≤ center K) (E : Subgroup M22) [IsElementaryAbelian 2 E] :
    IsElementaryAbelian 2 (E.comap f) := by
  have hs (x : E.comap f) : x ^ 2 = 1 := Subtype.ext
    (square_eq_one_of_central_double_extension f hf hk hcentral x
      (elemPow_eq_one_of_isElementaryAbelian _ x.property))
  exact
    { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
        (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

end Sporadic.Mathieu.M22CentralCover
