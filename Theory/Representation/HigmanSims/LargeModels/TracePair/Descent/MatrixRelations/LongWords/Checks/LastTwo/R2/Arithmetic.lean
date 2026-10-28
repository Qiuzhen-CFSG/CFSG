module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.Arithmetic
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Arithmetic

/-!
# Simultaneous row certificates over the fixed field of four elements

Two integers pack consecutive rows into lanes of width w. The generic binary
lane lemmas prove that multiplying the selected lane bits by a bounded row
copies it without carries. Applying this separately to the two coefficient
planes, including multiplication by omega, proves the exact packed row product.
The row count bound ensures that higher lanes cannot affect a lower input row.

A single checked `unpack` equality identifies every row of a saved block.
The R2 batch modules apply these theorems to the unchanged HSG1-f4r896aB0 data;
see `source/README.md` and `TracePair/source/README.md`. The imported arithmetic
from the degree-1408 development supplies only general natural-number lemmas.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.R2
open Certificates
open PackedBinaryRows.Lanes
open OrbitSpans.RowChecks

def laneRow (w i : Nat) (x : Packed.Row) : Packed.Row :=
  (lane w i x.1, lane w i x.2)

def copyRow (m x : Nat) (b : Packed.Row) : Packed.Row :=
  ((x &&& m) * b.1, (x &&& m) * b.2)

def scan (m : Nat) (x : Packed.Row) : Packed.Mat → Packed.Row
  | [] => (0, 0)
  | b :: bs => Packed.Base.addRow
      (Packed.Base.addRow (copyRow m x.1 b) (copyRow m x.2 (Packed.Base.timesT b)))
      (scan m (x.1 / 2, x.2 / 2) bs)

def Bounded (w : Nat) (b : Packed.Mat) : Prop :=
  ∀ r ∈ b, r.1 < 2 ^ w ∧ r.2 < 2 ^ w

lemma laneRow_add (w i : Nat) (x y : Packed.Row) :
    laneRow w i (Packed.Base.addRow x y) =
      Packed.Base.addRow (laneRow w i x) (laneRow w i y) := by
  simp [laneRow, Packed.Base.addRow, lane_xor]

lemma laneRow_copy (w n i x : Nat) (r : Packed.Row) (hw : 0 < w) (hi : i < n)
    (hr : r.1 < 2^w ∧ r.2 < 2^w) :
    laneRow w i (copyRow (mask w n) x r) =
      if x / (2^w)^i % 2 = 1 then r else (0,0) := by
  simp only [laneRow, copyRow, lane_mask_mul w n i x r.1 hw hi hr.1,
    lane_mask_mul w n i x r.2 hw hi hr.2]
  have h : x / (2^w)^i % 2 = 0 ∨ x / (2^w)^i % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

lemma timesT_bounded (w : Nat) (r : Packed.Row) (hr : r.1 < 2^w ∧ r.2 < 2^w) :
    (Packed.Base.timesT r).1 < 2^w ∧ (Packed.Base.timesT r).2 < 2^w :=
  ⟨hr.2, Nat.xor_lt_two_pow hr.1 hr.2⟩

def product (a : Packed.Row) : Packed.Mat → Packed.Row
  | [] => (0, 0)
  | b :: bs => Packed.Base.addRow
      (Packed.Base.addRow (if a.1 % 2 = 1 then b else (0, 0))
        (if a.2 % 2 = 1 then Packed.Base.timesT b else (0, 0)))
      (product (a.1 / 2, a.2 / 2) bs)

lemma product_eq_from (a : Packed.Row) (bs : Packed.Mat) (k : Nat) :
    product (a.1 / 2^k, a.2 / 2^k) bs = directProductFrom a bs k := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [product, directProductFrom, Nat.div_div_eq_div_mul, ← Nat.pow_succ, ih]

lemma product_eq (a : Packed.Row) (bs : Packed.Mat) :
    product a bs = Packed.rowProduct a bs := by
  simpa only [Nat.pow_zero, Nat.div_one, directProductFrom_eq, Packed.rowProduct] using
    product_eq_from a bs 0

lemma product_mod (a : Packed.Row) (w : Nat) (bs : Packed.Mat) (hlen : bs.length ≤ w) :
    product (a.1 % 2^w, a.2 % 2^w) bs = product a bs := by
  simp only [product_eq, Packed.rowProduct]
  suffices h : ∀ s, s + bs.length ≤ w →
      Packed.rowProductFrom (a.1 % 2^w, a.2 % 2^w) bs s = Packed.rowProductFrom a bs s
    from h 0 (by omega)
  intro s hs
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    have hs' : s < w := by simp only [List.length_cons] at hs; omega
    rw [Packed.rowProductFrom, Packed.rowProductFrom]
    simp only [Nat.testBit_mod_two_pow, hs', decide_true, Bool.true_and]
    rw [ih (by simp only [List.length_cons] at hlen; omega) (s+1)
      (by simp only [List.length_cons] at hs; omega)]

lemma scan_sound (w n i : Nat) (x : Packed.Row) (bs : Packed.Mat)
    (hw : 0 < w) (hi : i < n) (hb : Bounded w bs) :
    laneRow w i (scan (mask w n) x bs) =
      product (x.1 / (2^w)^i, x.2 / (2^w)^i) bs := by
  induction bs generalizing x with
  | nil => simp [scan, laneRow, lane, product]
  | cons b bs ih =>
    have hbb := hb b (by simp)
    rw [scan, laneRow_add, laneRow_add,
      laneRow_copy w n i x.1 b hw hi hbb,
      laneRow_copy w n i x.2 (Packed.Base.timesT b) hw hi (timesT_bounded w b hbb),
      ih (x.1/2, x.2/2) (by intro r hr; exact hb r (by simp [hr])), product]
    simp only [Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- A simultaneous scan proves the original packed product in every lane. -/
theorem rows_of_scan (w n : Nat) (bs : Packed.Mat) (x z : Packed.Row)
    (hw : 0 < w) (hlen : bs.length ≤ w) (hb : Bounded w bs)
    (h : scan (mask w n) x bs = z) (i : Fin n) :
    Packed.rowProduct (laneRow w i.val x) bs = laneRow w i.val z := by
  rw [← product_eq]
  change product (x.1 / (2^w)^i.val % 2^w, x.2 / (2^w)^i.val % 2^w) bs = _
  rw [product_mod (x.1 / (2^w)^i.val, x.2 / (2^w)^i.val) w bs hlen, ← scan_sound w n i.val x bs hw i.isLt hb, h]

/-- Decode a bounded sequence of lanes without repeated list indexing. -/
def unpack (w : Nat) : Nat → Packed.Row → Packed.Mat
  | 0, _ => []
  | n+1, x => (x.1 % 2^w, x.2 % 2^w) :: unpack w n (x.1 / 2^w, x.2 / 2^w)

lemma unpack_getD (w n : Nat) (x : Packed.Row) (i : Fin n) :
    (unpack w n x).getD i.val (0,0) = laneRow w i.val x := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [unpack, laneRow, lane_zero]
    · simpa only [unpack, Fin.val_succ, List.getD_cons_succ, laneRow, lane_succ]
        using ih (x.1 / 2^w, x.2 / 2^w) j

/-- Checking one whole consecutive list identifies every actual lane. -/
theorem lanes_of_unpack (w start count : Nat) (bs : Packed.Mat) (x : Packed.Row)
    (h : unpack w count x = (bs.drop start).take count) (i : Fin count) :
    laneRow w i.val x = bs.getD (start + i.val) (0,0) := by
  rw [← unpack_getD, h]
  simp [List.getD, List.getElem?_drop, i.isLt]

/-- A Boolean width certificate supplies both plane bounds for every row. -/
theorem bounded_of_check (w : Nat) (bs : Packed.Mat)
    (h : bs.all (fun r => decide (r.1 < 2^w ∧ r.2 < 2^w)) = true) : Bounded w bs := by
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- One original numerical row of a gate. -/
def RowAt (i : Fin 46) (r : Nat) : Prop :=
  Packed.rowProduct ((rowsAt (inputs i).1).getD r (0,0)) (rowsAt (inputs i).2) =
    (rowsAt (i.val + 2)).getD r (0,0)

/-- Fourteen consecutive blocks of 64 rows cover the whole literal matrix. -/
theorem productCheck_of_batches (i : Fin 46)
    (h : ∀ b : Fin 14, ∀ r : Fin 64, RowAt i (64 * b.val + r.val)) : ProductCheck i := by
  apply productCheck_of_rows
  intro r
  have hb : r.val / 64 < 14 := by omega
  have hr : r.val % 64 < 64 := Nat.mod_lt _ (by decide)
  have he : 64 * (r.val / 64) + r.val % 64 = r.val := by omega
  simpa only [RowAt, he] using h ⟨r.val / 64, hb⟩ ⟨r.val % 64, hr⟩

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.R2
