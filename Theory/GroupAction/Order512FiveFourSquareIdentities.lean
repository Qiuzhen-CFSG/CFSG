module

public import Theory.GroupAction.Order512FiveFourSquarePairing
public import Mathlib.Tactic.Group

/-!
# The square-commutator identity on the actual two layers

The polarization of squaring is the commutator modulo the center. When the
derived subgroup is elementary, the commutator of a square is the corresponding
iterated commutator. These identities give the additional constraint on the
paired quadratic map needed to produce a nonidentity zero.
-/

namespace Theory.GroupAction.Order512FiveFour
open Subgroup
open scoped commutatorElement IsMulCommutative

private theorem square_mul_of_central {L : Type*} [Group L] (x y : L)
    (hx : x ^ 2 ∈ center L) (hc : ⁅x, y⁆ ∈ center L) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x, y⁆ := by
  symm
  calc
    x ^ 2 * y ^ 2 * ⁅x, y⁆ = ⁅x, y⁆ * (x ^ 2 * y ^ 2) :=
      mem_center_iff.mp hc _
    _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
      simp only [commutatorElement_def, mul_assoc]
    _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by
      rw [mem_center_iff.mp hx]
    _ = (x * y) ^ 2 := by simp only [pow_two]; group

variable {P : Type*} [Group P] (D : Subgroup P) [D.Normal]
    [IsElementaryAbelian 2 D]
    (hD : D ≤ Subgroup.upperCentralSeries P 2)
    (hsq : ∀ x : P, x ^ 2 ∈ D) (hcomm : _root_.commutator P ≤ D)

/-- Polarizing the descended square map gives the actual commutator coset. -/
public theorem square_polar (x y : P) :
    let q := elementarySecondCenterSquare D hD hsq
    let π := QuotientGroup.mk' D
    q (π x * π y) * q (π x) * q (π y) =
      QuotientGroup.mk' ((center P).subgroupOf D)
        ⟨⁅x, y⁆, hcomm (commutator_mem_commutator (mem_top x) (mem_top y))⟩ := by
  let p := QuotientGroup.mk' (center P)
  have hcentral (d : P) (hd : d ∈ D) : p d ∈ center (P ⧸ center P) := by
    have hh := hD hd
    rw [← Subgroup.comap_upperCentralSeries_quotient_center 1,
      Subgroup.upperCentralSeries_one] at hh
    exact hh
  have hc : ⁅x, y⁆ ∈ D := hcomm (commutator_mem_commutator (mem_top x) (mem_top y))
  have hmod : p ((x * y) ^ 2) = p (x ^ 2 * y ^ 2 * ⁅x, y⁆) := by
    simpa only [map_pow, map_mul, map_commutatorElement] using
      square_mul_of_central (p x) (p y)
        (by simpa only [map_pow] using hcentral _ (hsq x))
        (by simpa only [map_commutatorElement] using hcentral _ hc)
  let πD := QuotientGroup.mk' ((center P).subgroupOf D)
  have hrel : πD ⟨(x * y) ^ 2, hsq (x * y)⟩ =
      πD (⟨x ^ 2, hsq x⟩ * ⟨y ^ 2, hsq y⟩ * ⟨⁅x, y⁆, hc⟩) := by
    apply QuotientGroup.eq.mpr
    change ((x * y) ^ 2)⁻¹ * (x ^ 2 * y ^ 2 * ⁅x, y⁆) ∈ center P
    exact QuotientGroup.eq.mp hmod
  dsimp only
  rw [← map_mul, elementarySecondCenterSquare_apply,
    elementarySecondCenterSquare_apply, elementarySecondCenterSquare_apply]
  change πD ⟨(x * y) ^ 2, _⟩ * πD ⟨x ^ 2, _⟩ * πD ⟨y ^ 2, _⟩ = πD ⟨⁅x, y⁆, _⟩
  rw [hrel, map_mul, map_mul]
  have hs (d : D) : πD d * πD d = 1 := by
    rw [← map_mul, ← pow_two,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 D) d, map_one]
  calc
    _ = (πD ⟨x ^ 2, _⟩ * πD ⟨x ^ 2, _⟩) *
        (πD ⟨y ^ 2, _⟩ * πD ⟨y ^ 2, _⟩) * πD ⟨⁅x, y⁆, _⟩ := by ac_rfl
    _ = _ := by rw [hs, hs, one_mul, one_mul]

include hcomm in
/-- The literal square pairing satisfies the iterated commutator constraint. -/
public theorem squarePairing_commutator
    (eZ : center P ≃* Multiplicative (ZMod 2)) (v w : P ⧸ D) :
    let B := squarePairing D hD eZ
    let q := elementarySecondCenterSquare D hD hsq
    B w (q v) = B v (q (v * w) * q v * q w) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D w
  dsimp only
  rw [square_polar D hD hsq hcomm, elementarySecondCenterSquare_apply,
    squarePairing_apply, squarePairing_apply]
  congr 1
  apply Subtype.ext
  change ⁅x ^ 2, y⁆ = ⁅⁅x, y⁆, x⁆
  have hc : ⁅x, y⁆ ∈ D := hcomm (commutator_mem_commutator (mem_top x) (mem_top y))
  have hci : ⁅x, y⁆⁻¹ = ⁅x, y⁆ := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hc)
  have ht : ⁅x, ⁅x, y⁆⁆ ∈ center P := by
    rw [← commutatorElement_inv]
    exact (center P).inv_mem (bracket_mem D hD ⟨⁅x, y⁆, hc⟩ x)
  have hti : ⁅x, ⁅x, y⁆⁆⁻¹ = ⁅x, ⁅x, y⁆⁆ := by
    have hs : (⟨⁅x, ⁅x, y⁆⁆, ht⟩ : center P) ^ 2 = 1 := by
      apply eZ.injective
      simp only [map_pow, map_one]
      exact pow_card_eq_one
    have hs' : ⁅x, ⁅x, y⁆⁆ ^ 2 = 1 := congrArg (center P).subtype hs
    exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs')
  calc
    ⁅x ^ 2, y⁆ = ⁅x, ⁅x, y⁆⁆ := by
      rw [pow_two, commutatorElement_mul_left_eq_conj_mul]
      conv_rhs => rw [commutatorElement_def, hci]
    _ = ⁅⁅x, y⁆, x⁆ := by rw [← hti, commutatorElement_inv]

end Theory.GroupAction.Order512FiveFour
