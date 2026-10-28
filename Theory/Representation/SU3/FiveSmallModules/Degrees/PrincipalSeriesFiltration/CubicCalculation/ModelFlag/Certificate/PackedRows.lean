module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Data
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Checked packed arithmetic for cubic matrix certificates

A row is represented by two natural-number bit planes, its real and omega
coefficients over F₂. XOR adds rows; multiplying by omega sends (x,y) to
(y,x+y). The proofs below connect every packed operation with the original
quadratic coefficient algebra. Thus subsequent finite checks use Lean's kernel
on compact natural numbers, without trusting a script or native evaluation.

These operations certify the cubic principal-series matrices used for
Guralnick–Malle, Proposition 4.3, p.10.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.Certificate.Packed
abbrev Row := ℕ × ℕ
def entry (r : Row) (j : ℕ) : CoefficientField :=
  ⟨if r.1.testBit j then 1 else 0, if r.2.testBit j then 1 else 0⟩
def add (r s : Row) : Row := (r.1 ^^^ s.1, r.2 ^^^ s.2)
def scale (a b : Bool) (r : Row) : Row :=
  ((if a then r.1 else 0) ^^^ (if b then r.2 else 0),
   (if a then r.2 else 0) ^^^ (if b then r.1 ^^^ r.2 else 0))
theorem entry_zero (j : ℕ) : entry (0,0) j = 0 := by simp [entry]; rfl
theorem entry_add (r s : Row) (j : ℕ) : entry (add r s) j = entry r j + entry s j := by
  simp only [entry, add, Nat.testBit_xor]
  cases r.1.testBit j <;> cases r.2.testBit j <;>
    cases s.1.testBit j <;> cases s.2.testBit j <;> decide

theorem entry_scale (a b : Bool) (r : Row) (j : ℕ) :
    entry (scale a b r) j = (⟨if a then 1 else 0, if b then 1 else 0⟩ : CoefficientField) * entry r j := by
  cases a <;> cases b <;>
    simp only [entry, scale, Bool.false_eq_true, ↓reduceIte, Nat.testBit_xor, Nat.zero_testBit] <;>
    cases r.1.testBit j <;> cases r.2.testBit j <;> decide

def sum : List Row → Row
  | [] => (0,0)
  | r :: rs => add r (sum rs)
theorem entry_sum (rs : List Row) (j : ℕ) : entry (sum rs) j = (rs.map (entry · j)).sum := by
  induction rs with
  | nil => exact entry_zero j
  | cons r rs ih => simp only [sum, entry_add, List.map_cons, List.sum_cons, ih]

def mul {m n : ℕ} (a : Fin m → Row) (b : Fin n → Row) : Fin m → Row :=
  fun i => sum (List.ofFn fun k : Fin n => scale ((a i).1.testBit k.val) ((a i).2.testBit k.val) (b k))
def matrix {m : ℕ} (n : ℕ) (a : Fin m → Row) : Matrix (Fin m) (Fin n) CoefficientField :=
  fun i j => entry (a i) j.val

theorem matrix_mul {m n p : ℕ} (a : Fin m → Row) (b : Fin n → Row) :
    matrix p (mul a b) = matrix n a * matrix p b := by
  apply Matrix.ext
  intro i j
  simp only [matrix, mul, entry_sum, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact entry_scale _ _ _ _

theorem matrix_zero (m n : ℕ) : matrix n (fun _ : Fin m => (0,0)) = 0 := by
  apply Matrix.ext
  intro i j
  exact entry_zero j.val

def identity (n : ℕ) : Fin n → Row := fun i => (2 ^ i.val, 0)
theorem matrix_identity (n : ℕ) : matrix n (identity n) = 1 := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [matrix, entry, identity]
    rfl
  · have hij : i.val ≠ j.val := fun h' => h (Fin.ext h')
    simp [matrix, entry, identity, hij, h]
    rfl

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.Certificate.Packed
