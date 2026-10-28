module

public import Theory.GroupTheory.ElementarySecondCenterSquareQuadratic
public import Theory.ElementaryAbelian.BinaryPairingDuality
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# The actual paired layers of an elementary second center

Commutators pair the quotient by an elementary second-center subgroup with
that subgroup modulo the whole center. Equal layer orders make the pairing
perfect. Its evaluations use the original group elements throughout.
-/

public noncomputable section
namespace Theory.GroupAction.Order512FiveFour
open Subgroup
open scoped commutatorElement IsMulCommutative

variable {P : Type*} [Group P] (D : Subgroup P) [D.Normal]
    [IsElementaryAbelian 2 D]
    (hD : D ≤ Subgroup.upperCentralSeries P 2)
    (eZ : center P ≃* Multiplicative (ZMod 2))

omit [D.Normal] [IsElementaryAbelian 2 D] in
include hD in
theorem bracket_mem (d : D) (x : P) : ⁅(d : P), x⁆ ∈ center P := by
  simpa only [Subgroup.upperCentralSeries_one] using
    (Subgroup.mem_upperCentralSeries_succ_iff.mp (hD d.property) x)

private def rawPairing : D →* (P →* Multiplicative (ZMod 2)) where
  toFun d := {
    toFun x := eZ ⟨⁅(d : P), x⁆, bracket_mem D hD d x⟩
    map_one' := by simp
    map_mul' x y := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      change ⁅(d : P), x * y⁆ = ⁅(d : P), x⁆ * ⁅(d : P), y⁆
      rw [commutatorElement_mul_right_eq_mul_conj,
        mul_assoc ⁅(d : P), x⁆ x ⁅(d : P), y⁆,
        mem_center_iff.mp (bracket_mem D hD d y) x]
      simp only [← mul_assoc, mul_inv_cancel_right] }
  map_one' := by
    ext x
    change eZ ⟨⁅(1 : P), x⁆, _⟩ = 1
    simp
  map_mul' d c := by
    ext x
    change eZ ⟨⁅(d : P) * (c : P), x⁆, _⟩ =
      eZ ⟨⁅(d : P), x⁆, _⟩ * eZ ⟨⁅(c : P), x⁆, _⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change ⁅(d : P) * (c : P), x⁆ = ⁅(d : P), x⁆ * ⁅(c : P), x⁆
    rw [commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp (bracket_mem D hD c x) (d : P), mul_inv_cancel_right]
    exact (mem_center_iff.mp (bracket_mem D hD c x) ⁅(d : P), x⁆).symm

omit [D.Normal] [IsElementaryAbelian 2 D] in
private theorem rawPairing_eq_one (d : D) (x : P) :
    rawPairing D hD eZ d x = 1 ↔ Commute (d : P) x := by
  change eZ ⟨⁅(d : P), x⁆, _⟩ = 1 ↔ _
  rw [← eZ.map_one, eZ.injective.eq_iff, Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm

private def firstPairing : (D ⧸ (center P).subgroupOf D) →*
    (P →* Multiplicative (ZMod 2)) :=
  QuotientGroup.lift _ (rawPairing D hD eZ) (by
    intro z hz
    ext x
    exact (rawPairing_eq_one D hD eZ z x).mpr (mem_center_iff.mp hz x).symm)

private def reversePairing : (D ⧸ (center P).subgroupOf D) →*
    ((P ⧸ D) →* Multiplicative (ZMod 2)) where
  toFun w := QuotientGroup.lift D (firstPairing D hD eZ w) (by
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective ((center P).subgroupOf D) w
    intro x hx
    exact (rawPairing_eq_one D hD eZ d x).mpr
      (setLike_mul_comm (s := D) d.property hx))
  map_one' := by
    apply MonoidHom.ext
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D v
    change firstPairing D hD eZ 1 x = 1
    simp
  map_mul' u v := by
    apply MonoidHom.ext
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D w
    change firstPairing D hD eZ (u * v) x =
      firstPairing D hD eZ u x * firstPairing D hD eZ v x
    rw [map_mul]
    rfl

/-- The literal central commutator, with the whole-group quotient first. -/
def squarePairing : (P ⧸ D) →*
    ((D ⧸ (center P).subgroupOf D) →* Multiplicative (ZMod 2)) :=
  (reversePairing D hD eZ).flip

theorem squarePairing_apply (x : P) (d : D) :
    squarePairing D hD eZ (QuotientGroup.mk' D x)
      (QuotientGroup.mk' ((center P).subgroupOf D) d) =
        eZ ⟨⁅(d : P), x⁆, bracket_mem D hD d x⟩ := by rfl

private theorem reversePairing_injective : Function.Injective (reversePairing D hD eZ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro w hw
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective ((center P).subgroupOf D) w
  apply (QuotientGroup.eq_one_iff d).mpr
  apply mem_center_iff.mpr
  intro x
  have hh := congrArg (fun f : (P ⧸ D) →* Multiplicative (ZMod 2) =>
    f (QuotientGroup.mk' D x)) hw
  exact ((rawPairing_eq_one D hD eZ d x).mp hh).symm.eq

/-- Equal finite elementary layers make the central commutator pairing perfect. -/
theorem squarePairing_bijective [Finite P] [IsElementaryAbelian 2 (P ⧸ D)]
    (hcard : Nat.card (D ⧸ (center P).subgroupOf D) = Nat.card (P ⧸ D)) :
    Function.Bijective (squarePairing D hD eZ) := by
  let : IsElementaryAbelian 2 (D ⧸ (center P).subgroupOf D) := {
    exponent_dvd_p := (MonoidHom.exponent_dvd (f := QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)).trans
      (IsElementaryAbelian.exponent_dvd_p 2 D) }
  exact MonoidHom.binary_pairing_flip_bijective (reversePairing D hD eZ) hcard
    (reversePairing_injective D hD eZ)

/-- A square is orthogonal to its own coset. -/
theorem squarePairing_self (hsq : ∀ x : P, x ^ 2 ∈ D) (v : P ⧸ D) :
    squarePairing D hD eZ v (elementarySecondCenterSquare D hD hsq v) = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D v
  rw [elementarySecondCenterSquare_apply, squarePairing_apply]
  rw [← eZ.map_one, eZ.injective.eq_iff]
  apply Subtype.ext
  change ⁅x ^ 2, x⁆ = 1
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Commute.pow_left (Commute.refl x) 2)

end Theory.GroupAction.Order512FiveFour
