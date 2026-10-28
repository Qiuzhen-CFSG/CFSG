module

public import Theory.SpecificGroups.Lyons.Atlas111Arithmetic

/-!
# Carry-free row arithmetic for the Lyons word certificates

Rows are packed in radix 3125. A product coefficient is at most
`111 * 4 * 4 = 1776`, so natural-number row accumulation has no carries.
The encoding lemmas recover each coefficient, and `decode_mul` transfers
closed Boolean row checks to matrix multiplication over `ZMod 5`.
`decode_repack` connects these rows to the original base-five ATLAS data.

Source and certificate generation: `../Atlas111Source/` and
`../Atlas111WordSource/Generate.py`. No computation outside Lean is trusted.
-/

namespace Lyons.Atlas111WordCertificate

@[expose] public def allRows (p : Fin 111 → Bool) : Bool :=
  Atlas111Certificate.allBelow 111 fun i => p (Fin.ofNat 111 i)

public theorem allRows_sound {p : Fin 111 → Bool} (h : allRows p = true) (i : Fin 111) :
    p i = true := by
  have hi := Atlas111Certificate.allBelow_sound h i.val i.isLt
  have heq : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [heq] using hi

@[expose] public def radix : ℕ := 3125

@[expose] public def digit (a j : ℕ) : ℕ := a / radix ^ j % radix

@[expose] public def encode : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + radix * encode n (fun j => f (j + 1))

public theorem digit_succ (a j : ℕ) : digit a (j + 1) = digit (a / radix) j := by
  simp only [digit, pow_succ', Nat.div_div_eq_div_mul]

public theorem encode_digits (n a : ℕ) (ha : a < radix ^ n) :
    encode n (digit a) = a := by
  induction n generalizing a with
  | zero =>
    simp only [pow_zero] at ha
    have : a = 0 := by omega
    simp [encode, this]
  | succ n ih =>
    have hdiv : a / radix < radix ^ n := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < radix)).mpr
      simpa only [pow_succ, Nat.mul_comm] using ha
    simp only [encode, digit_succ, ih _ hdiv]
    simpa only [digit, pow_zero, Nat.div_one] using Nat.mod_add_div a radix

public theorem digit_encode (n : ℕ) (f : ℕ → ℕ) (hf : ∀ j < n, f j < radix)
    (j : ℕ) (hj : j < n) : digit (encode n f) j = f j := by
  induction n generalizing f j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
      simp only [digit, pow_zero, Nat.div_one, encode, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (hf 0 (by omega))
    | succ j =>
      rw [digit_succ, encode, Nat.add_mul_div_left _ _ (by decide : 0 < radix)]
      rw [Nat.div_eq_of_lt (hf 0 (by omega)), zero_add]
      exact ih (fun k => f (k + 1)) (fun k hk => hf (k + 1) (by omega)) j (by omega)

public theorem encode_sum {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → ℕ → ℕ) :
    encode n (fun j => ∑ k ∈ s, f k j) = ∑ k ∈ s, encode n (f k) := by
  induction n generalizing f with
  | zero => simp [encode]
  | succ n ih => simp only [encode, ih, Finset.sum_add_distrib, Finset.mul_sum]

public theorem encode_mul (n c : ℕ) (f : ℕ → ℕ) :
    encode n (fun j => c * f j) = c * encode n f := by
  induction n generalizing f with
  | zero => simp [encode]
  | succ n ih => simp only [encode, ih, Nat.mul_add, Nat.mul_left_comm]

@[expose] public def rowProduct (a : ℕ) (rows : Fin 111 → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rowProduct a rows n + digit a n * rows (Fin.ofNat 111 n)

public theorem rowProduct_eq (a : ℕ) (rows : Fin 111 → ℕ) (n : ℕ) :
    rowProduct a rows n = ∑ k : Fin n, digit a k.val * rows (Fin.ofNat 111 k.val) := by
  induction n with
  | zero => simp [rowProduct]
  | succ n ih => simp only [rowProduct, ih, Fin.sum_univ_castSucc,
      Fin.val_castSucc, Fin.val_last]

@[expose] public def digitsEq : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n + 1, a, b => (a % radix % 5 == b % radix) && digitsEq n (a / radix) (b / radix)

public theorem digitsEq_sound (n a b : ℕ) (h : digitsEq n a b = true) :
    ∀ j < n, digit a j % 5 = digit b j := by
  induction n generalizing a b with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [digitsEq, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj
    cases j with
    | zero => simpa [digit] using h.1
    | succ j => simpa only [digit_succ] using ih _ _ h.2 j (by omega)

@[expose] public def small : ℕ → ℕ → Bool
  | 0, a => a == 0
  | n + 1, a => (a % radix < 5) && small n (a / radix)

public theorem small_sound (n a : ℕ) (h : small n a = true) :
    a < radix ^ n ∧ ∀ j < n, digit a j < 5 := by
  induction n generalizing a with
  | zero =>
    simp only [small, beq_iff_eq] at h
    subst a
    exact ⟨by simp, by intro j hj; omega⟩
  | succ n ih =>
    simp only [small, Bool.and_eq_true, decide_eq_true_eq] at h
    have hi := ih _ h.2
    constructor
    · rw [pow_succ']
      simpa only [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul (by decide : 0 < radix)).mp hi.1
    · intro j hj
      cases j with
      | zero => simpa [digit] using h.1
      | succ j => simpa only [digit_succ] using hi.2 j (by omega)

@[expose] public def decode (rows : Fin 111 → ℕ) : AtlasMatrix :=
  fun i j => (digit (rows i) j.val : ZMod 5)

public theorem rowProduct_digit (a : ℕ) (rows : Fin 111 → ℕ)
    (ha : small 111 a = true) (hb : ∀ k, small 111 (rows k) = true) (j : Fin 111) :
    digit (rowProduct a rows 111) j.val =
      ∑ k : Fin 111, digit a k.val * digit (rows k) j.val := by
  have hrep (k : Fin 111) : encode 111 (digit (rows k)) = rows k :=
    encode_digits _ _ (small_sound _ _ (hb k)).1
  have heq : rowProduct a rows 111 =
      encode 111 (fun l => ∑ k : Fin 111, digit a k.val * digit (rows k) l) := by
    rw [encode_sum]
    simp only [encode_mul, hrep, rowProduct_eq]
    congr 1
    funext k
    have hk : Fin.ofNat 111 k.val = k := by ext; exact Nat.mod_eq_of_lt k.isLt
    rw [hk]
  rw [heq]
  apply digit_encode _ _ _ _ j.isLt
  intro l hl
  have hbound : (∑ k : Fin 111, digit a k.val * digit (rows k) l) ≤
      ∑ _k : Fin 111, 16 := by
    apply Finset.sum_le_sum
    intro k _
    have hak := (small_sound _ _ ha).2 k.val k.isLt
    have hbk := (small_sound _ _ (hb k)).2 l hl
    have hak' : digit a k.val ≤ 4 := by omega
    have hbk' : digit (rows k) l ≤ 4 := by omega
    exact Nat.mul_le_mul hak' hbk'
  have hsum : (∑ _k : Fin 111, (16 : ℕ)) = 1776 := by simp
  rw [hsum] at hbound
  exact lt_of_le_of_lt hbound (by decide : 1776 < radix)

public theorem decode_mul (a b c : Fin 111 → ℕ)
    (ha : ∀ i, small 111 (a i) = true) (hb : ∀ i, small 111 (b i) = true)
    (h : ∀ i, digitsEq 111 (rowProduct (a i) b 111) (c i) = true) :
    decode a * decode b = decode c := by
  ext i j
  change (∑ k : Fin 111, (digit (a i) k.val : ZMod 5) *
      (digit (b k) j.val : ZMod 5)) = (digit (c i) j.val : ZMod 5)
  simp only [← Nat.cast_mul]
  rw [← Nat.cast_sum]
  rw [← rowProduct_digit _ _ (ha i) hb j, ← ZMod.natCast_mod,
    digitsEq_sound _ _ _ (h i) j.val j.isLt]

@[expose] public def repack : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, a => a % 5 + radix * repack n (a / 5)

public theorem digit_repack (n a j : ℕ) (hj : j < n) :
    digit (repack n a) j = a / 5 ^ j % 5 := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
      simp only [digit, pow_zero, Nat.div_one, repack, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt a (by decide)) (by decide : 5 < radix))
    | succ j =>
      rw [digit_succ, repack, Nat.add_mul_div_left _ _ (by decide : 0 < radix)]
      rw [Nat.div_eq_of_lt (lt_trans (Nat.mod_lt a (by decide))
        (by decide : 5 < radix)), zero_add, ih _ _ (by omega)]
      simp only [Nat.div_div_eq_div_mul, pow_succ']

public theorem decode_repack (rows packed : Fin 111 → ℕ)
    (h : ∀ i, repack 111 (rows i) = packed i) :
    decode packed = (fun i j => (rows i / 5 ^ j.val : ℕ) : AtlasMatrix) := by
  ext i j
  change (digit (packed i) j.val : ZMod 5) = (rows i / 5 ^ j.val : ℕ)
  rw [← h i, digit_repack _ _ _ j.isLt, ZMod.natCast_mod]

end Lyons.Atlas111WordCertificate
