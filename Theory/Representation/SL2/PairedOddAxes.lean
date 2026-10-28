module

public import Theory.SpecificGroups.SL2.NaturalStabilizer
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Odd subgroups fixing a vector on paired natural planes

In characteristic two, an SL₂ matrix fixing a nonzero vector has square one.
An odd-order group fixing that vector therefore has trivial image. Applied to
a nonzero coordinate of a vector in two natural planes, this puts the original
odd subgroup in one coordinate kernel, without any restriction to field order
four or exponent three.

Source application: Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public section
open Matrix
open scoped MatrixGroups
namespace Representation.SL2.PairedOddAxes
variable {F H : Type*} [Field F] [CharP F 2] [Group H]

/-- An odd subgroup fixing a nonzero natural vector has trivial image. -/
theorem le_kernel_of_nonzero_fixed
    (q : H →* SL(2,F)) (P : Subgroup H) (hodd : Odd (Nat.card P))
    (v : Fin 2 → F) (hv : v ≠ 0)
    (hfix : ∀ p ∈ P, (q p).val *ᵥ v = v) : P ≤ q.ker := by
  intro p hp
  change q p = 1
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [← hodd.coprime_two_left.gcd_eq_one]
  apply Nat.dvd_gcd
  · exact orderOf_dvd_of_pow_eq_one
      (Matrix.SL2.pow_two_eq_one_of_nonzero_fixed (q p) v hv (hfix p hp))
  · apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_one] using
      congrArg (fun x : P => q x) (pow_card_eq_one' (x := ⟨p,hp⟩))

/-- A common nonzero fixed vector places the original odd subgroup in one
coordinate kernel of the paired natural action. -/
theorem le_kernel_or_le_kernel_of_nonzero_fixed
    (q₁ q₂ : H →* SL(2,F)) (P : Subgroup H) (hodd : Odd (Nat.card P))
    (v : (Fin 2 → F) × (Fin 2 → F)) (hv : v ≠ 0)
    (hfix : ∀ p ∈ P, ((q₁ p).val *ᵥ v.1, (q₂ p).val *ᵥ v.2) = v) :
    P ≤ q₁.ker ∨ P ≤ q₂.ker := by
  by_cases hv₁ : v.1 = 0
  · right
    exact le_kernel_of_nonzero_fixed q₂ P hodd v.2
      (fun hz => hv (Prod.ext hv₁ hz))
      (fun p hp => congrArg Prod.snd (hfix p hp))
  · left
    exact le_kernel_of_nonzero_fixed q₁ P hodd v.1 hv₁
      (fun p hp => congrArg Prod.fst (hfix p hp))

end Representation.SL2.PairedOddAxes
