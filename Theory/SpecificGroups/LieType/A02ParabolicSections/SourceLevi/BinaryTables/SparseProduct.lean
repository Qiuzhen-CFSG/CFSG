module
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.BinaryTables

/-!
# Sparse binary row products with exact support certificates

A list of positions represents a row by XOR of the corresponding powers of
two. Induction proves that XOR of the selected right-hand rows is ordinary
matrix multiplication after decoding. Exact support-mask checks validate the
left matrix; checked sparse products validate the result. No assumption about
uniqueness or completeness of a supplied support is needed beyond the checked
mask equality. Exceptional root-word certificates use this to avoid iterating
through zero matrix entries.

Source: elementary arithmetic over F₂, applied to the GLS3 §1.12 root matrices.
-/

@[expose] public section
namespace Theory.SpecificGroups.LieType.SourceLevi.BinaryTables
open Thompson.BinaryMatrix
variable {n : ℕ}

def supportMask : List (Fin n) → ℕ
  | [] => 0
  | k :: ks => (2 ^ k.val) ^^^ supportMask ks

def supportProduct (b : Array ℕ) : List (Fin n) → ℕ
  | [] => 0
  | k :: ks => b[k.val]! ^^^ supportProduct b ks

private theorem bit_single (i k : Fin n) :
    bit (2 ^ i.val) k.val = if k = i then 1 else 0 := by
  by_cases h : k = i
  · subst k; simp [bit]
  · have hv : i.val ≠ k.val := fun he => h (Fin.ext he.symm)
    simp [bit, h, hv]

theorem bit_supportProduct (ks : List (Fin n)) (b : Array ℕ) (j : Fin n) :
    bit (supportProduct b ks) j.val =
      ∑ k : Fin n, bit (supportMask ks) k.val * bit b[k.val]! j.val := by
  induction ks with
  | nil => simp [supportProduct, supportMask, bit]
  | cons k ks ih =>
    simp only [supportProduct, supportMask, bit_xor, ih, add_mul,
      Finset.sum_add_distrib, bit_single]
    simp

theorem decode_support_mul (a b c : Array ℕ) (support : Fin n → List (Fin n))
    (ha : ∀ i, supportMask (support i) = a[i.val]!)
    (hc : ∀ i, supportProduct b (support i) = c[i.val]!) :
    decode n a * decode n b = decode n c := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = bit c[i.val]! j.val
  rw [← ha i, ← bit_supportProduct, hc]

theorem decode_support_mul_one (a b : Array ℕ) (support : Fin n → List (Fin n))
    (ha : ∀ i, supportMask (support i) = a[i.val]!)
    (hc : ∀ i, supportProduct b (support i) = 2 ^ i.val) :
    decode n a * decode n b = 1 := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = _
  rw [← ha i, ← bit_supportProduct, hc, bit_single]
  simp [Matrix.one_apply, eq_comm]

end Theory.SpecificGroups.LieType.SourceLevi.BinaryTables
