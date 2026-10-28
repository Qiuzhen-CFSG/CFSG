module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# A computable field of order nine

The quadratic algebra over `ZMod 3` with `i² = -1` is a field: its defining
quadratic has no root in `ZMod 3`. Its elements are pairs of residues, so
matrix identities over this field can be checked by kernel reduction.
Quadratic conjugation is the cube map. The cardinality identifies the field
with Mathlib's `GaloisField 3 2`, and this identification respects Frobenius.

Source: the quadratic-algebra construction and uniqueness of finite fields.
-/

namespace FiniteField

/-- The field `F₃[i]`, with `i² = -1`, represented by pairs of residues. -/
public abbrev Nine := QuadraticAlgebra (ZMod 3) (-1) 0

namespace Nine

public instance quadratic_has_no_root :
    Fact (∀ r : ZMod 3, r ^ 2 ≠ -1 + 0 * r) := ⟨by decide⟩

/-- The enumeration is part of the computational interface. -/
public instance : Fintype Nine :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3) (QuadraticAlgebra.equivProd (-1) 0).symm

@[simp] public theorem card : Fintype.card Nine = 9 := by decide

@[simp] public theorem natCard : Nat.card Nine = 9 := by
  rw [Nat.card_eq_fintype_card, card]

/-- The quadratic involution is the nontrivial finite-field Frobenius. -/
public theorem star_eq_cube (x : Nine) : star x = x ^ 3 := by
  have h : ∀ x : Nine, star x = x ^ 3 := by decide
  exact h x

/-- Identification with the field used by the standard unitary matrix model. -/
public noncomputable def equivGaloisField : Nine ≃+* GaloisField 3 2 := by
  letI := Fintype.ofFinite (GaloisField 3 2)
  apply FiniteField.ringEquivOfCardEq
  rw [card, ← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by decide)]
  norm_num

/-- Coefficient transport carries quadratic conjugation to cube Frobenius. -/
public theorem equivGaloisField_star (x : Nine) :
    equivGaloisField (star x) = equivGaloisField x ^ 3 := by
  rw [star_eq_cube, map_pow]

end Nine
end FiniteField
