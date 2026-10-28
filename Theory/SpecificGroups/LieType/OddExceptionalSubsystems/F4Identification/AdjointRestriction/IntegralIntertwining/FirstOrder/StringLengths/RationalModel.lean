module
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Rational coordinates for the folded E6 root strings

These rational vectors reproduce the coordinate formulas of `Exceptional` and
`AdjointRestriction.Coordinates`. A pair root has two nonzero coordinates, each
±1; a half root has all coordinates ±½. The E6 predicate adds even negative
parity and the two orthogonality equations. The F4 predicate includes pair,
unit and half roots. `bottom` checks the first three downward steps.

The real-coordinate and actual root-string interpretations are proved in the
parent `StringLengths` module; no root-pairing coefficient is defined here.
Sources: GLS3 §§2.2–2.6; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction.StringLengths

def sign (b : Bool) : ℚ := if b then 1 else -1
def unit {n : ℕ} (i : Fin n) : Fin n → ℚ := fun k => if k = i then 1 else 0
def pair {n : ℕ} (i j : Fin n) (s t : Bool) : Fin n → ℚ :=
  fun k => sign s * unit i k + sign t * unit j k
def half {n : ℕ} (ε : Fin n → Bool) : Fin n → ℚ := fun k => sign (ε k) / 2

def isPair {n : ℕ} (x : Fin n → ℚ) : Prop :=
  (∀ k, x k = -1 ∨ x k = 0 ∨ x k = 1) ∧
    (Finset.univ.filter (fun k => x k ≠ 0)).card = 2
instance decidableIsPair {n : ℕ} (x : Fin n → ℚ) : Decidable (isPair x) := inferInstanceAs (Decidable (_ ∧ _))
def isHalf {n : ℕ} (x : Fin n → ℚ) : Prop := ∀ k, x k = 1/2 ∨ x k = -(1/2)
instance decidableIsHalf {n : ℕ} (x : Fin n → ℚ) : Decidable (isHalf x) := inferInstanceAs (Decidable (∀ _k, _ ∨ _))
def E6 (x : Fin 8 → ℚ) : Prop :=
  (isPair x ∨ (isHalf x ∧ (Finset.univ.filter (fun k => x k < 0)).card % 2 = 0)) ∧ x 0 + x 1 = 0 ∧ x 1 - x 2 = 0
instance decidableE6 (x : Fin 8 → ℚ) : Decidable (E6 x) := inferInstanceAs (Decidable ((_ ∨ _) ∧ _ ∧ _))
def F4 (x : Fin 4 → ℚ) : Prop :=
  isPair x ∨ (∃ i : Fin 4, x = unit i ∨ x = -unit i) ∨ isHalf x
instance decidableF4 (x : Fin 4 → ℚ) : Decidable (F4 x) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))
def simple6 : Fin 6 → (Fin 8 → ℚ) := ![
 ![1/2,-(1/2),-(1/2),-(1/2),-(1/2),-(1/2),-(1/2),1/2],
 ![0,0,0,0,0,0,1,-1], ![0,0,0,0,0,1,-1,0],
 ![0,0,0,0,0,0,1,1], ![0,0,0,0,1,-1,0,0], ![0,0,0,1,-1,0,0,0]]
def simple4 : Fin 4 → (Fin 4 → ℚ) := ![
 ![0,1,-1,0], ![0,0,1,-1], ![0,0,0,1], ![1/2,-(1/2),-(1/2),-(1/2)]]
def project (x : Fin 8 → ℚ) : Fin 4 → ℚ := ![
 (5*x 0+x 1+x 2+x 3)/2, (x 4+x 5+x 6+x 7)/2,
 (x 4+x 5-x 6-x 7)/2, (x 4-x 5+x 6-x 7)/2]
def bottom {n : ℕ} (S : (Fin n → ℚ) → Prop) [DecidablePred S]
    (s r : Fin n → ℚ) : ℕ :=
  if S (r-s) then if S (r-2 • s) then if S (r-3 • s) then 3 else 2 else 1 else 0

def check (x : Fin 8 → ℚ) (i : Fin 4) : Prop :=
 (∑ j : Fin 6, if (![3,2,1,0,2,3] : Fin 6 → Fin 4) j = i then bottom E6 (simple6 j) x else 0) = bottom F4 (simple4 i) (project x)
instance decidableCheck (x : Fin 8 → ℚ) (i : Fin 4) : Decidable (check x i) := inferInstanceAs (Decidable (_ = _))


end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction.StringLengths
