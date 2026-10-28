module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.Roots
import Mathlib.Tactic

/-!
# Folded coroot coordinates and their characters

Coordinates on the actual E6 diagonal torus are constant on the two paired
nodes {0,5}, {1,4}, and independent on fixed nodes {2}, {3}. The root
characters are computed from the literal E6 Cartan matrix. On the first
three coordinates their matrix has determinant two; hence they separate
parameters over a binary field when the fourth coordinate is one.

These formulas prepare the root-normalizer obstruction of Aschbacher–Smith
A.2.18, printed p.40, on the pinned graph-field carrier of GLS3 §§2.2–2.4
(`refs/KGroup/GLS3/chapter2.tex`). Torus membership in the subgroup generated
by two-elements and faithfulness after its center quotient are separate
steps; no folded-model identification is asserted here.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace TwistedE6.TheoremDRootNormalizer
noncomputable section
attribute [local instance] Classical.decEq

/-- Labels of the four diagram orbits. -/
def orbitIndex : Fin 6 → Fin 4 := ![0, 1, 2, 3, 1, 0]

/-- Inclusion of units from the literal Frobenius fixed subfield. -/
def coefficientUnit (m : ℕ) : (FixedField m)ˣ →* (CoefficientField 2 m)ˣ :=
  Units.map (fixedField m).subtype.toMonoidHom

@[simp] theorem coefficientUnit_val (m : ℕ) (u : (FixedField m)ˣ) :
    (coefficientUnit m u : CoefficientField 2 m) = ((u : FixedField m) : CoefficientField 2 m) := rfl

theorem coefficientUnit_injective (m : ℕ) : Function.Injective (coefficientUnit m) := by
  intro u v h
  apply Units.ext
  apply Subtype.ext
  exact congrArg Units.val h

/-- Four coroot coordinates, constant on each diagram orbit. -/
def foldedParameters (m : ℕ) : (Fin 4 → (FixedField m)ˣ) →* (Base.support → (CoefficientField 2 m)ˣ) where
  toFun a j := coefficientUnit m (a (orbitIndex (typeE6RootPairing_baseEquiv.symm j)))
  map_one' := by ext j; exact map_one _
  map_mul' a c := by ext j; exact map_mul _ _ _

@[simp] theorem foldedParameters_simple (m : ℕ) (a : Fin 4 → (FixedField m)ˣ) (j : Fin 6) :
    foldedParameters m a (simpleIndex j) = coefficientUnit m (a (orbitIndex j)) := by
  simp [foldedParameters, simpleIndex]

/-- The diagonal homomorphism in the original matrix-unit carrier. -/
def foldedTorusMatrix (m : ℕ) : (Fin 4 → (FixedField m)ˣ) →* AmbientGroup 2 m :=
  (ExceptionalSplit.TheoremDRootNormalizer.torusMatrixHom (P := Pairing)).comp (foldedParameters m)

def foldedCharacter {m : ℕ} (a : Fin 4 → (FixedField m)ˣ) : Fin 4 → (FixedField m)ˣ :=
  ![a 0 ^ 2 * (a 1)⁻¹,
    (a 0)⁻¹ * a 1 ^ 2 * (a 2)⁻¹,
    (a 1 ^ 2)⁻¹ * a 2 ^ 2 * (a 3)⁻¹,
    (a 2)⁻¹ * a 3 ^ 2]

theorem foldedParameters_scale (m : ℕ) (a : Fin 4 → (FixedField m)ˣ) (j : Fin 6) :
    integralChevalleyRootScale (P := Pairing) (foldedParameters m a) (simpleIndex j) =
      coefficientUnit m (foldedCharacter a (orbitIndex j)) := by
  unfold integralChevalleyRootScale
  rw [← Equiv.prod_comp typeE6RootPairing_baseEquiv]
  have hp (k : Fin 6) : Pairing.pairingIn ℤ (simpleIndex j) (simpleIndex k) =
      typeE6CartanMatrix j k := typeE6RootPairing_base_cartan_apply j k
  simp only [foldedParameters_simple, hp]
  fin_cases j <;> simp [Fin.prod_univ_succ, orbitIndex, foldedCharacter,
    typeE6CartanMatrix, map_mul, map_inv, map_pow] <;> simp only [pow_two, mul_inv_rev] <;> ac_rfl

/-- The first three folded characters have determinant two once coordinate 3 is one. -/
theorem foldedCharacter_separate (m : ℕ) (a : Fin 4 → (FixedField m)ˣ)
    (h3 : a 3 = 1) (h : ∀ i : Fin 3, foldedCharacter a i.castSucc = 1) : a = 1 := by
  have h0 : a 0 ^ 2 = a 1 := by
    apply mul_inv_eq_one.mp
    simpa [foldedCharacter] using h 0
  have h1 : (a 0)⁻¹ * a 1 ^ 2 * (a 2)⁻¹ = 1 := by
    simpa [foldedCharacter] using h 1
  have h2sq : a 1 ^ 2 = a 2 ^ 2 := by
    apply inv_mul_eq_one.mp
    simpa [foldedCharacter, h3] using h 2
  have h2 : a 1 = a 2 := by
    apply Units.ext
    apply (frobenius_inj (FixedField m) 2)
    exact congrArg Units.val h2sq
  rw [← h2, pow_two, mul_assoc, mul_inv_cancel_right] at h1
  have h01 : a 0 = a 1 := inv_mul_eq_one.mp h1
  have ha0 : a 0 = 1 := by
    apply mul_left_cancel (a := a 0)
    simpa only [pow_two, mul_one] using h0.trans h01.symm
  have ha1 := h01.symm.trans ha0
  have ha2 := h2.symm.trans ha1
  funext i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2
  · exact h3

/-- The literal torus on three coordinates, with the fourth coordinate one. -/
def threeCoordinates (m : ℕ) : (Fin 3 → (FixedField m)ˣ) →* (Fin 4 → (FixedField m)ˣ) where
  toFun a := ![a 0, a 1, a 2, 1]
  map_one' := by ext i; fin_cases i <;> rfl
  map_mul' a b := by ext i; fin_cases i <;> simp

@[simp] theorem threeCoordinates_last (m : ℕ) (a : Fin 3 → (FixedField m)ˣ) :
    threeCoordinates m a 3 = 1 := rfl

theorem threeCoordinates_injective (m : ℕ) : Function.Injective (threeCoordinates m) := by
  intro a b hab
  funext i
  have h := congrFun hab i.castSucc
  fin_cases i <;> exact h

end
end TwistedE6.TheoremDRootNormalizer
