module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.FieldUnits
public import BenderSuzuki.MatrixGroups.Unitary

/-!
# The exact special unitary model for the twisted cubic torus

We use the identity Hermitian form on three coordinates over the chosen
quadratic extension of F, with the actual relative Frobenius as conjugation.
Its square is the identity; when |F| = p its action is x ↦ x^p.
The group used by the torus construction is `standardForm.specialSubgroup`,
the literal determinant-one subgroup of GL₃. No scalar quotient is taken.

This fixes a common interface for the two independent constructions needed
in `TwistedCubicTorus`: realization of the sextic-field units in this SU₃,
and the faithful embedding of this SU₃ in the split-octonion G₂ model.
Neither embedding is assumed to exist by this module.

Source application: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408,
and GLS III §6.1, via the unitary subsystem of G₂.
-/

@[expose] public section

namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus
open BenderSuzuki.MatrixGroups
noncomputable section
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Relative Frobenius on the quadratic coefficient field. -/
def quadraticConj : Quadratic F p ≃+* Quadratic F p :=
  (FiniteField.Extension.frob F p 2).toRingEquiv

theorem quadraticConj_apply (hF : Nat.card F = p) (x : Quadratic F p) :
    quadraticConj F p x = x ^ p := by
  change FiniteField.Extension.frob F p 2 x = _
  rw [FiniteField.Extension.frob_apply, hF]

theorem quadraticConj_involutive : Function.Involutive (quadraticConj F p) := by
  intro x
  change FiniteField.Extension.frob F p 2 (FiniteField.Extension.frob F p 2 x) = x
  rw [FiniteField.Extension.frob_apply, FiniteField.Extension.frob_apply, ← pow_mul,
    ← pow_two, ← FiniteField.natCard_extension F p 2]
  let := Fintype.ofFinite (Quadratic F p)
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/-- The identity Hermitian form with its genuine quadratic conjugation. -/
def standardForm : HermitianForm 3 (Quadratic F p) where
  conj := quadraticConj F p
  conj_involutive := quadraticConj_involutive F p
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

theorem standardForm_conj (hF : Nat.card F = p) (x : Quadratic F p) :
    (standardForm F p).conj x = x ^ p := quadraticConj_apply F p hF x

theorem standardForm_matrix : (standardForm F p).form = 1 := rfl

end
end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus
