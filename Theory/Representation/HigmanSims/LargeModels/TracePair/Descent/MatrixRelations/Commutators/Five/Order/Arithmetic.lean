module
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Products
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Arithmetic

/-!
# Simultaneous GF(4) products on packed rows

Each lane stores one row's coefficient plane. The proved binary lane mask
copies a right-factor plane into each selected lane without carries. Four
such copies implement multiplication in Four, where omega² = omega + 1;
XOR implements addition. Extracting each lane gives `Streaming.product`
on the original rows, with no assumption on the matrix product.

The numerical consumers certify the three fixed products for the fifth
power of C from the ATLAS HSG1-f4r896aB0 data. See `source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.OrderArithmetic
open Certificates Packed PackedBinaryRows.Lanes

def laneRow (w i : Nat) (x : Row) : Row := (lane w i x.1, lane w i x.2)

def spread (m x : Nat) (r : Row) : Row := ((x &&& m) * r.1, (x &&& m) * r.2)

def scan (m : Nat) (x : Row) : Mat → Row
  | [] => (0, 0)
  | r :: rs => Base.addRow
      (Base.addRow (spread m x.1 r) (Base.timesT (spread m x.2 r)))
      (scan m (x.1 / 2, x.2 / 2) rs)

lemma laneRow_add (w i : Nat) (x y : Row) :
    laneRow w i (Base.addRow x y) = Base.addRow (laneRow w i x) (laneRow w i y) := by
  simp only [laneRow, Base.addRow, lane_xor]

lemma laneRow_timesT (w i : Nat) (x : Row) :
    laneRow w i (Base.timesT x) = Base.timesT (laneRow w i x) := by
  simp only [laneRow, Base.timesT, lane_xor]

lemma laneRow_spread (w n i x : Nat) (r : Row) (hw : 0 < w) (hi : i < n)
    (hr : r.1 < 2 ^ w ∧ r.2 < 2 ^ w) :
    laneRow w i (spread (mask w n) x r) =
      if x / (2 ^ w) ^ i % 2 = 1 then r else (0, 0) := by
  simp only [laneRow, spread, lane_mask_mul w n i x _ hw hi hr.1,
    lane_mask_mul w n i x _ hw hi hr.2]
  have h : x / (2 ^ w) ^ i % 2 = 0 ∨ x / (2 ^ w) ^ i % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

/-- Extracting a lane recovers the ordinary streamed row product. -/
lemma scan_sound (w n i : Nat) (x : Row) (rs : Mat) (hw : 0 < w) (hi : i < n)
    (hrs : ∀ r ∈ rs, r.1 < 2 ^ w ∧ r.2 < 2 ^ w) :
    laneRow w i (scan (mask w n) x rs) =
      Streaming.product (x.1 / (2 ^ w) ^ i, x.2 / (2 ^ w) ^ i) rs := by
  induction rs generalizing x with
  | nil => simp [scan, laneRow, lane, Streaming.product]
  | cons r rs ih =>
    rw [scan, laneRow_add, laneRow_add, laneRow_timesT,
      laneRow_spread w n i x.1 r hw hi (hrs r (by simp)),
      laneRow_spread w n i x.2 r hw hi (hrs r (by simp)),
      ih _ (by intro r hr; exact hrs r (by simp [hr])), Streaming.product]
    by_cases h : x.2 / (2 ^ w) ^ i % 2 = 1 <;>
      simp [h, Base.timesT, Nat.div_div_eq_div_mul, Nat.mul_comm]

lemma product_mod (x : Row) (w : Nat) (rs : Mat) (hlen : rs.length ≤ w) :
    Streaming.product (x.1 % 2 ^ w, x.2 % 2 ^ w) rs = Streaming.product x rs := by
  rw [Streaming.product_eq, Streaming.product_eq]
  suffices h : ∀ s, s + rs.length ≤ w →
      rowProductFrom (x.1 % 2 ^ w, x.2 % 2 ^ w) rs s = rowProductFrom x rs s from
    h 0 (by omega)
  intro s hs
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    have hs' : s < w := by simp only [List.length_cons] at hs; omega
    rw [rowProductFrom, rowProductFrom, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    simp only [hs', decide_true, Bool.true_and]
    rw [ih (by simp only [List.length_cons] at hlen; omega) (s + 1)
      (by simp only [List.length_cons] at hs; omega)]

/-- A checked scan gives every literal row equation in the batch. -/
theorem rows_of_scan (w n : Nat) (rs : Mat) (x z : Row) (hw : 0 < w)
    (hlen : rs.length ≤ w) (hrs : ∀ r ∈ rs, r.1 < 2 ^ w ∧ r.2 < 2 ^ w)
    (h : scan (mask w n) x rs = z) (i : Fin n) :
    Streaming.product (laneRow w i.val x) rs = laneRow w i.val z := by
  change Streaming.product
    (x.1 / (2 ^ w) ^ i.val % 2 ^ w, x.2 / (2 ^ w) ^ i.val % 2 ^ w) rs = _
  rw [product_mod (x.1 / (2 ^ w) ^ i.val, x.2 / (2 ^ w) ^ i.val) _ _ hlen,
    ← scan_sound w n i.val x rs hw i.isLt hrs, h]
end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.OrderArithmetic
