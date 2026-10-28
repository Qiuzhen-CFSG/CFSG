module

public import Theory.LinearAlgebra.PackedBinaryRows

/-!
# Simultaneous packed binary row products

A lane has width `w`. The mask has one low bit in each lane, so multiplying
`x &&& mask w n` by a row smaller than `2^w` copies that row into precisely
the selected lanes, without carries between them. XOR and shifting then
compute `n` row products simultaneously. `rows_of_scan` recovers each ordinary
`PackedBinaryRows.listProduct`; no numerical oracle is used.

This arithmetic supports the four exact products for the first two relations
of the retained ATLAS HSG1-P1.M. See `source/README.md` in this directory.
-/

@[expose] public section

namespace PackedBinaryRows.Lanes

/-- One selector bit per lane. -/
def mask (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + 2 ^ w * mask w n

/-- Extract one base-`2^w` digit. -/
def lane (w i x : Nat) : Nat := x / (2 ^ w) ^ i % 2 ^ w

/-- Simultaneous XOR row action on all selected lanes. -/
def scan (m x : Nat) : List Nat → Nat
  | [] => 0
  | r :: rs => ((x &&& m) * r) ^^^ scan m (x / 2) rs

lemma lane_zero (w x : Nat) : lane w 0 x = x % 2 ^ w := by
  simp [lane]

lemma lane_succ (w i x : Nat) : lane w (i+1) x = lane w i (x / 2 ^ w) := by
  simp only [lane, Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm (2 ^ w)]

lemma lane_xor (w i x y : Nat) : lane w i (x ^^^ y) = lane w i x ^^^ lane w i y := by
  simp only [lane, ← Nat.pow_mul, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow]

lemma mask_mul_split (w n x r : Nat) (hw : 0 < w) :
    (x &&& mask w (n+1)) * r =
      (x % 2) * r + 2 ^ w * (((x / 2 ^ w) &&& mask w n) * r) := by
  have hb : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hm0 : mask w (n+1) % 2 ^ w = 1 := by
    simp only [mask, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have hmd : mask w (n+1) / 2 ^ w = mask w n := by
    rw [mask, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]
  have hlow : (x &&& mask w (n+1)) % 2 ^ w = x % 2 := by
    rw [Nat.and_mod_two_pow, hm0, Nat.and_one_is_mod]
    have he : w = (w - 1) + 1 := by omega
    have hd : 2 ∣ 2 ^ w := by
      rw [he, Nat.pow_succ]
      exact Nat.dvd_mul_left 2 _
    exact Nat.mod_mod_of_dvd x hd
  have hhigh : (x &&& mask w (n+1)) / 2 ^ w = (x / 2 ^ w) &&& mask w n := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hmd]
  have h := Nat.mod_add_div (x &&& mask w (n+1)) (2 ^ w)
  rw [hlow, hhigh] at h
  rw [← h, Nat.add_mul, Nat.mul_assoc]

lemma lane_mask_mul (w n i x r : Nat) (hw : 0 < w) (hi : i < n)
    (hr : r < 2 ^ w) :
    lane w i ((x &&& mask w n) * r) = (x / (2 ^ w) ^ i % 2) * r := by
  induction n generalizing i x with
  | zero => omega
  | succ n ih =>
    have hb : 0 < 2 ^ w := Nat.two_pow_pos w
    have hc : (x % 2) * r < 2 ^ w := by
      have h : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases h with h | h <;> simp [h, hr, hb]
    rw [mask_mul_split w n x r hw]
    cases i with
    | zero =>
      simp only [lane_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc,
        Nat.pow_zero, Nat.div_one]
    | succ i =>
      rw [lane_succ, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hc, Nat.zero_add,
        ih i (x / 2 ^ w) (by omega)]
      simp only [Nat.pow_succ, Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm (2 ^ w)]

lemma listProduct_shift (x s t : Nat) (rs : List Nat) :
    listProduct x (s + t) rs = listProduct (x >>> s) t rs := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih =>
    simp only [listProduct, Nat.testBit_shiftRight]
    rw [Nat.add_assoc, ih]

/-- Every lane of the simultaneous scan is the ordinary binary row action. -/
theorem scan_sound (w n i x : Nat) (rs : List Nat) (hw : 0 < w) (hi : i < n)
    (hrs : ∀ r ∈ rs, r < 2 ^ w) :
    lane w i (scan (mask w n) x rs) = listProduct (x / (2 ^ w) ^ i) 0 rs := by
  induction rs generalizing x with
  | nil => simp [scan, lane, listProduct]
  | cons r rs ih =>
    rw [scan, lane_xor, lane_mask_mul w n i x r hw hi (hrs r (by simp)),
      ih (x / 2) (by intro r hr; exact hrs r (by simp [hr])), listProduct]
    have ht : listProduct (x / (2 ^ w) ^ i) 1 rs =
        listProduct (x / 2 / (2 ^ w) ^ i) 0 rs := by
      have h := listProduct_shift (x / (2 ^ w) ^ i) 1 0 rs
      simpa only [Nat.add_zero, Nat.shiftRight_eq_div_pow, Nat.pow_one,
        Nat.div_div_eq_div_mul, Nat.mul_comm] using h
    rw [ht, Nat.testBit_zero]
    have h : x / (2 ^ w) ^ i % 2 = 0 ∨ x / (2 ^ w) ^ i % 2 = 1 := by omega
    rcases h with h | h <;> simp [h]

lemma listProduct_mod (x w : Nat) (rs : List Nat) (hlen : rs.length ≤ w) :
    listProduct (x % 2 ^ w) 0 rs = listProduct x 0 rs := by
  suffices h : ∀ s, s + rs.length ≤ w →
      listProduct (x % 2 ^ w) s rs = listProduct x s rs from h 0 (by omega)
  intro s hs
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    have hs' : s < w := by simp only [List.length_cons] at hs; omega
    rw [listProduct, listProduct, Nat.testBit_mod_two_pow]
    simp only [hs', decide_true, Bool.true_and]
    rw [ih (by simp only [List.length_cons] at hlen; omega) (s+1)
      (by simp only [List.length_cons] at hs; omega)]

/-- A checked simultaneous scan supplies every row in its batch. -/
theorem rows_of_scan (w n : Nat) (rs : List Nat) (x z : Nat) (hw : 0 < w)
    (hlen : rs.length ≤ w) (hrs : ∀ r ∈ rs, r < 2 ^ w)
    (h : scan (mask w n) x rs = z) (i : Fin n) :
    listProduct (lane w i.val x) 0 rs = lane w i.val z := by
  rw [lane, listProduct_mod _ _ _ hlen, ← scan_sound w n i.val x rs hw i.isLt hrs, h]
end PackedBinaryRows.Lanes
