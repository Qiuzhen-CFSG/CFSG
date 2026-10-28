module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Specializing cubic certificates to the original coefficient field

The four-element field is realized by pairs over F₂ with ω² = 1 + ω.
For every characteristic-two field and every root z of X² + X + 1,
evaluation at z is an injective ring homomorphism. Thus a certificate over
these pairs can be specialized without assuming an embedding or restricting
the original coefficient field to GF(4).

This is the coefficient step for the cubic principal series in
Guralnick–Malle, Proposition 4.3, p.10.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag

abbrev CoefficientField := QuadraticAlgebra (ZMod 2) 1 1

instance coefficientIrreducible : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) :=
  ⟨by decide⟩

theorem omega_cube : (QuadraticAlgebra.omega : CoefficientField) ^ 3 = 1 := by
  decide

theorem omega_ne_one : (QuadraticAlgebra.omega : CoefficientField) ≠ 1 := by
  decide

/-- The coefficient homomorphism is constructed from the cubic scalar,
rather than supplied as a further hypothesis. -/
noncomputable def evaluate {K : Type*} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) : CoefficientField →+* K := by
  letI : Algebra (ZMod 2) K := (ZMod.castHom (by decide : 2 ∣ 2) K).toAlgebra
  apply (QuadraticAlgebra.lift ⟨z, ?_⟩).toRingHom
  change z * z = (1 : ZMod 2) • (1 : K) + (1 : ZMod 2) • z
  simp only [one_smul]
  have hc (x : K) : x + x = 0 := CharTwo.add_self_eq_zero x
  calc
    z * z = (z ^ 2 + z + 1) + (1 + z) := by
      rw [pow_two]
      linear_combination -(hc z) - hc 1
    _ = 1 + z := by rw [hz, zero_add]

@[simp] theorem evaluate_omega {K : Type*} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) :
    evaluate z hz QuadraticAlgebra.omega = z := by
  change (ZMod.castHom (by decide : 2 ∣ 2) K) 0 * 1 +
    (ZMod.castHom (by decide : 2 ∣ 2) K) 1 * z = z
  simp

theorem evaluate_injective {K : Type*} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) : Function.Injective (evaluate z hz) :=
  (evaluate z hz).injective

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
