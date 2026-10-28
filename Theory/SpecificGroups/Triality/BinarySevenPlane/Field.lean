module

public import Theory.SpecificGroups.Triality.Model.QTKEParameters
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# A cubic generator in the literal binary triality coefficient field

The extension field at q = 2 has eight elements. A unit other than one is
annihilated by one of the two irreducible cubic factors of the seventh
cyclotomic polynomial. Taking its inverse if necessary gives a root of
T³ + T + 1 in the original field, without choosing a different field model.
This is the scalar input to the explicit eleven-root-word construction of
the nonsplit seven-plane (ATLAS, printed p.89, triality at q = 2).
-/

public section
namespace Triality.Standard.BinarySevenPlane

private theorem exists_cubic_generator {F : Type*} [Field F] [Finite F]
    [CharP F 2] (hcard : Nat.card F = 8) :
    ∃ t : F, t ^ 3 = t + 1 := by
  classical
  let := Fintype.ofFinite F
  have hc : Fintype.card F = 8 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card
    (α := Fˣ) (by rw [Fintype.card_units, hc]; decide) 1
  let r : F := a
  have hr0 : r ≠ 0 := a.ne_zero
  have hr1 : r ≠ 1 := fun h => ha (Units.ext h)
  have hr7 : r ^ 7 = 1 := by
    simpa only [hc, Nat.reduceSub] using FiniteField.pow_card_sub_one_eq_one r hr0
  have hp : (r + 1) * ((r^3 + r + 1) * (r^3 + r^2 + 1)) = 0 := by
    calc
      _ = r^7 + 1 := by
        ring_nf
        simp [show (2 : F) = 0 from CharTwo.two_eq_zero,
          show (4 : F) = 0 by simpa only [show (2 : F) = 0 from CharTwo.two_eq_zero,
            zero_add] using (show (4 : F) = 2 + 2 by norm_num)]
      _ = 0 := by rw [hr7, CharTwo.add_self_eq_zero]
  have hne : r + 1 ≠ 0 := fun h => hr1 (CharTwo.add_eq_zero.mp h)
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hne) with h | h
  · refine ⟨r, ?_⟩
    rw [add_assoc, CharTwo.add_eq_zero] at h
    exact h
  · refine ⟨r⁻¹, ?_⟩
    have h' : r^3 + r^2 = 1 := CharTwo.add_eq_zero.mp h
    field_simp
    linear_combination -h'

/-- The cubic generator exists in the actual field used for `³D₄(2)`. -/
theorem exists_generator :
    ∃ t : ExtensionField (binaryParameters 1 Nat.zero_lt_one), t ^ 3 = t + 1 := by
  apply exists_cubic_generator
  simpa [binaryParameters, Parameters.q] using
    card_extensionField (binaryParameters 1 Nat.zero_lt_one)

/-- A chosen generator for the concrete root-word coefficients. -/
noncomputable def generator : ExtensionField (binaryParameters 1 Nat.zero_lt_one) :=
  exists_generator.choose

theorem generator_cubic : generator ^ 3 = generator + 1 := exists_generator.choose_spec

theorem generator_ne_zero : generator ≠ 0 := by
  intro h
  have hc := generator_cubic
  rw [h] at hc
  norm_num at hc

theorem generator_ne_one : generator ≠ 1 := by
  intro h
  have hc := generator_cubic
  rw [h] at hc
  rw [one_pow] at hc
  exact one_ne_zero (hc.trans (CharTwo.add_self_eq_zero
    (1 : ExtensionField (binaryParameters 1 Nat.zero_lt_one))))

end Triality.Standard.BinarySevenPlane
