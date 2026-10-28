module

public import Theory.SpecificGroups.SL3.PRegularClasses.TraceParameters
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Scalar determinant correction in dimension three

If three is coprime to the order of the field's unit group, every nonzero
determinant has a cube root. The corresponding scalar matrix commutes with
every matrix and has that determinant. This handles, in particular, the
field of two elements in the odd-order SL₃ class bound.

This is the elementary branch of the determinant correction needed for the
SL₃ specialization of GLS III, 2.8.2 and 2.8.6(a).
-/

namespace Theory.SpecificGroups.SL3.PRegularClasses

variable {F : Type*} [Field F]

/-- Scalar matrices realize all nonzero determinants when cubing the units
is bijective. No semisimplicity hypothesis is needed in this case. -/
public theorem exists_commuting_det_of_coprime (hc : (Nat.card F - 1).Coprime 3)
    (A : Matrix (Fin 3) (Fin 3) F) (d : F) (hd : d ≠ 0) :
    ∃ C : Matrix (Fin 3) (Fin 3) F, C * A = A * C ∧ C.det = d := by
  have hc' : (Nat.card Fˣ).Coprime 3 := by simpa only [Nat.card_units] using hc
  obtain ⟨c, hcd⟩ := hc'.pow_left_bijective.surjective (Units.mk0 d hd)
  refine ⟨(c : F) • 1, ?_, ?_⟩
  · simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  · simpa only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
      Units.val_pow_eq_pow_val, Units.val_mk0] using congrArg Units.val hcd

end Theory.SpecificGroups.SL3.PRegularClasses
