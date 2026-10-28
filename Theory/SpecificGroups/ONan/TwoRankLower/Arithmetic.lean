module
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.Arithmetic
/-!
# A Horner dot-product checker for O’Nan matrix certificates

The checker consumes packed base-seven digits successively. Its cast is the
ordinary matrix dot product, so checked Boolean row equations imply exact
matrix multiplication. This avoids repeated divisions by powers of seven in
the E₈ certificate used by Aschbacher–Smith A.2.12, printed p.36.
-/

@[expose] public section
namespace ONan.TwoRankLower.MatrixCheck
open Simplicity.TwoCertificate.Enumeration Simplicity.TwoCertificate.Enumeration.WordValues
def dot : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, a, b => (a % 7) * (b % 7) + dot n (a / 7) (b / 7)
theorem dot_eq (n a b : ℕ) : (dot n a b : ZMod 7) =
    ∑ j : Fin n, ((a / 7 ^ j.val : ℕ) : ZMod 7) * ((b / 7 ^ j.val : ℕ) : ZMod 7) := by
  induction n generalizing a b with
  | zero => simp [dot]
  | succ n ih =>
    simp only [dot, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, ih,
      Fin.sum_univ_succ, Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.div_div_eq_div_mul, pow_succ']
def checkRow (a bt c : Packed) (i : Fin 45) : Bool :=
  allBelow 45 fun j => dot 45 (a i) (bt (Fin.ofNat 45 j)) % 7 == (c i / 7^j) % 7
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
end ONan.TwoRankLower.MatrixCheck
