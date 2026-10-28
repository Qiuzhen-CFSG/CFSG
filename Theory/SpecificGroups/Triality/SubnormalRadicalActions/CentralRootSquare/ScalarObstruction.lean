module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.Coordinates

/-!
# A cubic-field obstruction for elementary central-radical images

The leading exchange coefficient is b(s,t) = s F(t) + F(s) t.
For any nonzero a, some s,d satisfy Tr(a F(b(sa,d))) = 1. Expanding
the trace converts the expression into a nonzero linear functional of d;
a Frobenius-moved s exists even when the base field has two elements.

This is the scalar part of the elementary-normal-subgroup argument. Applying
it to an actual group requires the separately proved iterated-commutator
root formula and must retain all higher radical coordinates.

Source: GLS3 2.4.5(b)(4) (`refs/KGroup/GLS3/chapter2.tex`), using the
checked folded coefficient and trace marking in `LeviCommutators`.
-/

public section
noncomputable section
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators

namespace Triality.Standard.Parabolics.CentralRootSquare

theorem iterated_pairing (P : Parameters) (a s d : ExtensionField P) :
    armsPairing P a (higherCoefficient P (s * a) d) =
      cubicTrace P ((fieldFrobenius P a * fieldFrobenius P (fieldFrobenius P a) *
        (fieldFrobenius P s + fieldFrobenius P (fieldFrobenius P s))) * d) := by
  apply Subtype.ext
  simp only [armsPairing, cubicTrace_coe, higherCoefficient, map_add, map_mul,
    fieldFrobenius_three]
  ring

theorem exists_iterated_pairing_one (P : Parameters) (hp : P.prime = 2)
    (a : ExtensionField P) (ha : a ≠ 0) :
    ∃ s d : ExtensionField P,
      armsPairing P a (higherCoefficient P (s * a) d) = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  obtain ⟨s, hs⟩ := ElementaryCentralKernel.exists_frobenius_moved P
  have hd : fieldFrobenius P s + fieldFrobenius P (fieldFrobenius P s) ≠ 0 := by
    intro h
    have he := CharTwo.add_eq_zero.mp h
    exact hs ((fieldFrobenius P).injective he).symm
  let k := fieldFrobenius P a * fieldFrobenius P (fieldFrobenius P a) *
    (fieldFrobenius P s + fieldFrobenius P (fieldFrobenius P s))
  have hk : k ≠ 0 := mul_ne_zero
    (mul_ne_zero ((map_ne_zero (fieldFrobenius P)).mpr ha)
      ((map_ne_zero (fieldFrobenius P)).mpr ((map_ne_zero (fieldFrobenius P)).mpr ha))) hd
  refine ⟨s, k⁻¹, ?_⟩
  rw [iterated_pairing]
  change cubicTrace P (k * k⁻¹) = 1
  rw [mul_inv_cancel₀ hk]
  exact cubicTrace_fixed P hp 1

theorem eq_zero_of_iterated_pairing (P : Parameters) (hp : P.prime = 2)
    (a : ExtensionField P)
    (h : ∀ s d, armsPairing P a (higherCoefficient P (s * a) d) = 0) : a = 0 := by
  by_contra ha
  obtain ⟨s, d, he⟩ := exists_iterated_pairing_one P hp a ha
  exact one_ne_zero (he.symm.trans (h s d))

end Triality.Standard.Parabolics.CentralRootSquare

end
