module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.Transport
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Arithmetic for the nine O'Nan word evaluations

Rows and columns are packed as base-seven natural numbers. The recursive dot
product is cast into `ZMod 7`, where it is the ordinary finite dot product.
Consequently closed Boolean row checks imply matrix multiplication identities.
This small checker follows the natural-number dot-product proof in
`Theory/SpecificGroups/Lyons/Atlas111Arithmetic.lean`; it uses no native evaluator.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration.WordValues

abbrev Packed := Fin 45 → ℕ
def decode (a : Packed) : Mat := fun i j => (a i / 7 ^ j.val : ℕ)
def dot : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, a, b => dot n a b + (a / 7^n % 7) * (b / 7^n % 7)
theorem dot_eq (n a b : ℕ) : (dot n a b : ZMod 7) =
    ∑ j : Fin n, ((a / 7 ^ j.val : ℕ) : ZMod 7) * ((b / 7 ^ j.val : ℕ) : ZMod 7) := by
  induction n with
  | zero => simp [dot]
  | succ n ih =>
    simp only [dot, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, ih,
      Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n+1, p => allBelow n p && p n
theorem allBelow_sound {n : ℕ} {p : ℕ → Bool} (h : allBelow n p = true) :
    ∀ i < n, p i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro i hi
    by_cases hin : i < n
    · exact ih h.1 i hin
    · have : i = n := by omega
      simpa [this] using h.2

def checkRow (a bt c : Packed) (i : Fin 45) : Bool :=
  allBelow 45 fun j =>
    dot 45 (a i) (bt (Fin.ofNat 45 j)) % 7 ==
      (c i / 7^j) % 7

theorem mul_sound (a b bt c : Packed)
    (ht : (decode bt).transpose = decode b)
    (h : ∀ i, checkRow a bt c i = true) : decode a * decode b = decode c := by
  ext i j
  have he := allBelow_sound (h i) j.val j.isLt
  have hj : Fin.ofNat 45 j.val = j := by ext; exact Nat.mod_eq_of_lt j.isLt
  simp only [hj, beq_iff_eq] at he
  rw [← ht, Matrix.mul_apply]
  change (∑ k : Fin 45, ((a i / 7^k.val : ℕ) : ZMod 7) *
    ((bt j / 7^k.val : ℕ) : ZMod 7)) = _
  rw [← dot_eq, ← ZMod.natCast_mod, he, ZMod.natCast_mod]
  rfl

/-- A finite Boolean traversal supplies each row check. -/
theorem allRows_sound (p : Fin 45 → Bool)
    (h : allBelow 45 (fun i => p (Fin.ofNat 45 i)) = true) (i : Fin 45) : p i = true := by
  have hi : Fin.ofNat 45 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [hi] using allBelow_sound h i.val i.isLt

end ONan.Simplicity.TwoCertificate.Enumeration.WordValues
