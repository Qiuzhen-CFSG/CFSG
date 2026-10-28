module
public import ABG.ChapterII.Section1.NormalForm

/-!
# Squares and conjugacy in the outer quasi-dihedral coset

In the quasi-dihedral presentation with cyclic generator `a` and involution
`b`, the square of `a^i*b` is the `i`th power of the central half-order
power of `a`. Conjugation by `a^((2^(n-3)+1)*t)` increases an outer exponent
by `2*t`, so outer elements whose exponents differ by an even number are
conjugate. The proof moves `b` across powers and reduces the resulting
exponent equality modulo `orderOf a`.

These calculations supply the involution and order-four conjugacy classes
in ABG Chapter II, §1, Lemma 1(i), article page 9 of
`refs/latex/alperin-brauer-gorenstein.tex`. The parameter `n ≥ 4` is the
Stellmacher presentation parameter, one larger than the article's.
-/
namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
/-- Squaring an outer element records the parity of its cyclic exponent. -/
public theorem outer_square {n : ℕ} (_hn : 4 ≤ n) (a b : G)
    (hb : orderOf b = 2) (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) (i : ℕ) :
    (a ^ i * b) ^ 2 = a ^ (2 ^ (n - 2) * i) := by
  have hbb : b * b = 1 := by simpa [pow_two, hb] using pow_orderOf_eq_one b
  have hp : 1 ≤ 2 ^ (n - 2) := Nat.one_le_pow _ _ (by omega)
  calc
    (a ^ i * b) ^ 2 = a ^ i * (b * a ^ i) * b := by simp only [pow_two, mul_assoc]
    _ = a ^ i * (a ^ ((2 ^ (n - 2) - 1) * i) * b) * b := by rw [move_pow a b _ hconj i]
    _ = a ^ (i + (2 ^ (n - 2) - 1) * i) := by rw [mul_assoc, mul_assoc, hbb, mul_one, ← pow_add]
    _ = a ^ (2 ^ (n - 2) * i) := by congr 1; nlinarith [Nat.sub_add_cancel hp]

/-- Adding an even number to an outer exponent preserves its conjugacy class. -/
public theorem outer_even_shift_isConj {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1))
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) (j t : ℕ) :
    IsConj (a ^ j * b) (a ^ (j + 2 * t) * b) := by
  let q := 2 ^ (n - 4)
  have hq : 0 < q := by dsimp [q]; positivity
  have hhalf : 2 ^ (n - 2) = 4 * q := by
    dsimp [q]
    rw [show n - 2 = (n - 4) + 2 by omega, pow_add]
    ring
  have hfull : 2 ^ (n - 1) = 8 * q := by
    dsimp [q]
    rw [show n - 1 = (n - 4) + 3 by omega, pow_add]
    ring
  let r := (2 * q + 1) * t
  have he : j + 2 * t + (2 ^ (n - 2) - 1) * r = (r + j) + (8 * q) * (q * t) := by
    rw [hhalf]
    dsimp [r]
    have hs : 4 * q - 1 + 1 = 4 * q := Nat.sub_add_cancel (by omega)
    have hs' := congrArg (· * ((2 * q + 1) * t)) hs
    nlinarith only [hs']
  have heq : a ^ (r + j) = a ^ (j + 2 * t + (2 ^ (n - 2) - 1) * r) := by
    apply pow_eq_pow_iff_modEq.mpr
    rw [ha, hfull, he]
    simp
  apply isConj_iff.mpr
  refine ⟨a ^ r, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  calc
    a ^ r * (a ^ j * b) = a ^ (r + j) * b := by rw [pow_add, mul_assoc]
    _ = a ^ (j + 2 * t + (2 ^ (n - 2) - 1) * r) * b := by rw [heq]
    _ = (a ^ (j + 2 * t) * b) * a ^ r := by simp only [pow_add, mul_assoc, move_pow a b _ hconj r]
end ABG.QuasiDihedral
