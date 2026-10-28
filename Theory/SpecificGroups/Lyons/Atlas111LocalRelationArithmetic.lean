module

public import Theory.SpecificGroups.Lyons.Atlas111Arithmetic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
/-!
# Packed row multiplication for the Lyons local relations

Rows are stored in base 2048. Since a product entry over the natural numbers
is at most `111 * 4 * 4 = 1776`, a sum of scaled packed rows has no carries
between coordinates. `product_eq` turns equality of normalized packed rows
into an equality of matrices over `ZMod 5`. All certificate checks use ordinary
kernel reduction; the data generator is not trusted.

This extends the base-five format of `Atlas111Source/Generate.py` for the
fixed words in `G2Five/AtlasPresentationSource/`.
-/

open scoped BigOperators
namespace Lyons.RelationCertificate
-- Fixed-base polynomial encoding, least significant coordinate first.
@[expose] public def pack : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + 2048 * pack n (fun i => f i.succ)

@[expose] public def digit (a j : ℕ) : ℕ := a / 2048 ^ j % 2048

public theorem digit_pack (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i < 2048)
    (j : Fin n) : digit (pack n f) j.val = f j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [digit, pack, Nat.add_mod, Nat.mod_eq_of_lt (hf 0)]
    · simp only [pack, digit, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2048),
        Nat.div_eq_of_lt (hf 0), zero_add]
      exact ih _ (fun i => hf i.succ) j

public theorem pack_digit (n a : ℕ) (ha : a < 2048 ^ n) :
    pack n (fun j => digit a j.val) = a := by
  induction n generalizing a with
  | zero => simp_all [pack]
  | succ n ih =>
    simp only [pack, digit, Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ]
    have hlt : a / 2048 < 2048 ^ n := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2048)).2
      simpa [pow_succ, Nat.mul_comm] using ha
    have he : (fun j : Fin n => a / 2048 ^ (j.val + 1) % 2048) =
        (fun j : Fin n => digit (a / 2048) j.val) := by
      funext j
      simp only [digit, pow_succ', Nat.div_div_eq_div_mul]
    rw [he, ih _ hlt]
    exact Nat.mod_add_div _ _

public theorem pack_sum {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → Fin n → ℕ) :
    pack n (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, pack n (f i) := by
  induction n with
  | zero => simp [pack]
  | succ n ih => simp only [pack, ih, Finset.mul_sum, Finset.sum_add_distrib]

public theorem pack_mul (n c : ℕ) (f : Fin n → ℕ) :
    pack n (fun j => c * f j) = c * pack n f := by
  induction n with
  | zero => simp [pack]
  | succ n ih => simp only [pack, ih]; ring



public abbrev Rows := Fin 111 → ℕ

@[expose] public def decode (a : Rows) : AtlasMatrix := fun i j => (digit (a i) j.val : ZMod 5)

@[expose] public def Valid (a : Rows) : Prop :=
  (∀ i, a i < 2048 ^ 111) ∧ (∀ i j : Fin 111, digit (a i) j.val < 5)

@[expose] public def rowSum : ℕ → ℕ → (ℕ → ℕ) → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => rowSum n a b + digit a n % 5 * b n

public theorem rowSum_eq (n a : ℕ) (b : ℕ → ℕ) :
    rowSum n a b = ∑ j : Fin n, digit a j.val % 5 * b j.val := by
  induction n with
  | zero => simp [rowSum]
  | succ n ih => simp [rowSum, ih, Fin.sum_univ_castSucc]

@[expose] public def normalize : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, a => a % 2048 % 5 + 2048 * normalize n (a / 2048)

public theorem normalize_eq (n a : ℕ) :
    normalize n a = pack n (fun j => digit a j.val % 5) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [normalize, pack, ih, digit, Fin.val_zero, pow_zero, Nat.div_one,
      Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]

public theorem digit_normalize (n a : ℕ) (j : Fin n) :
    digit (normalize n a) j.val = digit a j.val % 5 := by
  rw [normalize_eq, digit_pack]
  intro i
  exact (Nat.mod_lt _ (by decide : 0 < 5)).trans (by decide)

public theorem product_digit (a b : Rows) (hb : Valid b) (i j : Fin 111) :
    (digit (rowSum 111 (a i) (fun k => b (Fin.ofNat 111 k))) j.val : ZMod 5) =
      (decode a * decode b) i j := by
  have hn (k : Fin 111) : Fin.ofNat 111 k.val = k := by
    ext
    exact Nat.mod_eq_of_lt k.isLt
  have he : rowSum 111 (a i) (fun k => b (Fin.ofNat 111 k)) =
      pack 111 (fun j => ∑ k : Fin 111, digit (a i) k.val % 5 * digit (b k) j.val) := by
    rw [rowSum_eq, pack_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hn, pack_mul, pack_digit _ _ (hb.1 k)]
  have hbound (j : Fin 111) :
      (∑ k : Fin 111, digit (a i) k.val % 5 * digit (b k) j.val) < 2048 := by
    have hle : (∑ k : Fin 111, digit (a i) k.val % 5 * digit (b k) j.val) ≤
        ∑ _k : Fin 111, 16 := by
      apply Finset.sum_le_sum
      intro k _
      have h1 := Nat.mod_lt (digit (a i) k.val) (by decide : 0 < 5)
      have h2 := hb.2 k j
      nlinarith
    norm_num at hle
    omega
  rw [he, digit_pack _ _ hbound]
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod, Matrix.mul_apply, decode]

@[expose] public def checkProductRow (a b c : Rows) (i : Fin 111) : Bool :=
  normalize 111 (rowSum 111 (a i) (fun k => b (Fin.ofNat 111 k))) == c i

public theorem product_eq (a b c : Rows) (hb : Valid b)
    (h : ∀ i, checkProductRow a b c i = true) : decode a * decode b = decode c := by
  funext i j
  have hr := h i
  simp only [checkProductRow, beq_iff_eq] at hr
  rw [← product_digit a b hb i j, decode, ← hr, digit_normalize]
  simp only [ZMod.natCast_mod]

@[expose] public def checkValid (a : Rows) : Bool :=
  Atlas111Certificate.allBelow 111 fun i =>
    decide (a (Fin.ofNat 111 i) < 2048 ^ 111) &&
      Atlas111Certificate.allBelow 111 (fun j =>
        decide (digit (a (Fin.ofNat 111 i)) j < 5))

public theorem valid_of_check (a : Rows) (h : checkValid a = true) : Valid a := by
  have hh (i : Fin 111) : a i < 2048 ^ 111 ∧
      ∀ j : Fin 111, digit (a i) j.val < 5 := by
    have hi := Atlas111Certificate.allBelow_sound h i.val i.isLt
    have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
    simp only [he, Bool.and_eq_true, decide_eq_true_eq] at hi
    exact ⟨hi.1, fun j => of_decide_eq_true
      (Atlas111Certificate.allBelow_sound hi.2 j.val j.isLt)⟩
  exact ⟨fun i => (hh i).1, fun i => (hh i).2⟩

/-- A single closed check for all rows of a product. -/
@[expose] public def checkProduct (a b c : Rows) : Bool :=
  Atlas111Certificate.allBelow 111 fun i => checkProductRow a b c (Fin.ofNat 111 i)

public theorem product_of_check (a b c : Rows) (hb : checkValid b = true)
    (h : checkProduct a b c = true) : decode a * decode b = decode c := by
  apply product_eq a b c (valid_of_check b hb)
  intro i
  have hi := Atlas111Certificate.allBelow_sound h i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [he] using hi

/-- Assemble separately checked rows without repeating their arithmetic. -/
public theorem product_of_checked_rows (a b c : Rows) (hb : checkValid b = true)
    (h : ∀ i, checkProductRow a b c i = true) : decode a * decode b = decode c :=
  product_eq a b c (valid_of_check b hb) h

end Lyons.RelationCertificate
