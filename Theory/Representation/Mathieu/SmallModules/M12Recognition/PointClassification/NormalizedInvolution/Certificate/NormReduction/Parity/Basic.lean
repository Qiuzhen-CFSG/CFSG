module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Inputs
/-!
# Binary decoding for the original M11 norm rows

Packed natural-number XOR decodes to addition in `ZMod 2`. Balanced finite
folds connect the literal eleven-entry seeds and the published action matrix
to their coordinate vectors. Blocked lists keep the cancellation checker at
bounded recursion depth; their entries must be certified against the original
seed table before `row_of_masks` applies.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

@[expose] public section
open scoped BigOperators
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Parity
open Inputs

def unpack (n : Nat) : Coordinates := fun i => if n.testBit i.val then 1 else 0

theorem unpack_zero : unpack 0 = 0 := by ext i; simp [unpack]

theorem unpack_xor (a b : Nat) : unpack (a ^^^ b) = unpack a + unpack b := by
  funext i
  simp only [unpack, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide

theorem unpack_bit (i : Index) : unpack (2^i.val) = Pi.single i 1 := by
  ext j
  simp [unpack, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

def xorTree : Nat → (Nat → Nat) → Nat → Nat
  | 0, f, start => f start
  | d+1, f, start => xorTree d f start ^^^ xorTree d f (start + 2^d)

theorem unpack_xorTree (d : Nat) (f : Nat → Nat) (start : Nat) :
    unpack (xorTree d f start) = ∑ i ∈ Finset.range (2^d), unpack (f (start+i)) := by
  induction d generalizing start with
  | zero => simp [xorTree]
  | succ d ih =>
    rw [xorTree, unpack_xor, ih, ih, pow_succ, Nat.mul_two, Finset.sum_range_add]
    simp only [Nat.add_assoc]

def xorBound (d n : Nat) (f : Nat → Nat) : Nat :=
  xorTree d (fun i => if i < n then f i else 0) 0

theorem unpack_xorBound (d n : Nat) (hn : n ≤ 2^d) (f : Nat → Nat) :
    unpack (xorBound d n f) = ∑ i : Fin n, unpack (f i.val) := by
  rw [xorBound, unpack_xorTree, Fin.sum_univ_eq_sum_range (fun i => unpack (f i)) n]
  simp only [Nat.zero_add]
  calc
    _ = ∑ i ∈ Finset.range n, unpack (if i < n then f i else 0) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hn)
      intro i _ hin
      have hn' : ¬i < n := by simpa using hin
      simp [hn', unpack_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]

def seedCodeMask (code : Nat) : Nat :=
  xorBound 4 11 (fun t => 2^(((code >>> (13*t)) % 8192) % 7920))

def rawSeedMask (k : Nat) : Nat := seedCodeMask (tableEntry seedCodes k)

theorem unpack_rawSeedMask (k : Seed) : unpack (rawSeedMask k.val) = seedVector k := by
  rw [rawSeedMask, seedCodeMask, unpack_xorBound _ _ (by decide), seedVector]
  apply Finset.sum_congr rfl
  intro t _
  exact unpack_bit (seedEntry k t)

def packedColumn (s : Fin 2) (j : Fin 300) : Nat :=
  2^(leftIndex s j).val ^^^ xorBound 9 300 (fun i =>
    if (CertificateData.actionColumns s j).testBit i then
      2^(basisIndex (Fin.ofNat 300 i)).val else 0)

theorem unpack_packedColumn (s : Fin 2) (j : Fin 300) :
    unpack (packedColumn s j) = columnVector s j := by
  unfold packedColumn columnVector CertificateData.actionMatrix
  generalize leftIndex s j = l
  generalize basisIndex = b
  generalize CertificateData.actionColumns s j = c
  rw [unpack_xor, unpack_bit, unpack_xorBound _ _ (by decide)]
  have hs : ∀ x : Coordinates, -x = x := by
    intro x
    ext i
    exact CharTwo.neg_eq (x i)
  rw [sub_eq_add_neg, hs]
  have hsum : (∑ i : Fin 300, unpack (if c.testBit i.val then
      2^(b (Fin.ofNat 300 i.val)).val else 0)) =
      ∑ i : Fin 300, (if c.testBit i.val then (1 : ZMod 2) else 0) • Pi.single (b i) 1 := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : Fin.ofNat 300 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [hi]
    split_ifs <;> simp only [unpack_bit, unpack_zero, one_smul, zero_smul]
  rw [hsum]

def selectRows (w : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | offset, r :: rs => (if w.testBit offset then r else 0) ^^^ selectRows w (offset+1) rs

def selectBlocks (w : Nat) : Nat → List (List Nat) → Nat
  | _, [] => 0
  | offset, rs :: rest => selectRows w offset rs ^^^ selectBlocks w (offset+128) rest

theorem selectRows_append (w offset : Nat) (xs ys : List Nat) :
    selectRows w offset (xs ++ ys) =
      selectRows w offset xs ^^^ selectRows w (offset + xs.length) ys := by
  induction xs generalizing offset with
  | nil => simp [selectRows]
  | cons x xs ih =>
    simp only [List.cons_append, selectRows, ih, List.length_cons]
    rw [Nat.xor_assoc]
    simp only [Nat.add_assoc, Nat.add_comm 1]

theorem selectBlocks_flatten (w offset : Nat) (bs : List (List Nat))
    (hlen : ∀ b ∈ bs, b.length = 128) :
    selectBlocks w offset bs = selectRows w offset bs.flatten := by
  induction bs generalizing offset with
  | nil => rfl
  | cons b bs ih =>
    rw [selectBlocks, List.flatten_cons, selectRows_append, hlen b (by simp)]
    rw [ih _ (fun b hb => hlen b (by simp [hb]))]

theorem unpack_selectRows_range (w offset start n : Nat) (f : Nat → Nat) :
    unpack (selectRows w offset ((List.range' start n).map f)) =
      ∑ i ∈ Finset.range n, if w.testBit (offset+i) then unpack (f (start+i)) else 0 := by
  induction n generalizing offset start with
  | zero => simp [selectRows, unpack_zero]
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, selectRows, unpack_xor, ih,
      Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have hb : unpack (if w.testBit offset then f start else 0) =
        if w.testBit offset then unpack (f start) else 0 := by
      split_ifs <;> simp only [unpack_zero]
    rw [hb]
    simp only [Nat.add_assoc, Nat.add_comm 1]
    exact add_comm _ _

def paddedSeedMask (k : Nat) : Nat := if k < 7620 then rawSeedMask k else 0

/-- The zero witness has an immediate reduction. -/
def combinationMask (w : Nat) (bs : List (List Nat)) : Nat :=
  if w = 0 then 0 else selectBlocks w 0 bs

theorem unpack_combinationMask (bs : List (List Nat))
    (hlen : ∀ b ∈ bs, b.length = 128)
    (hrows : bs.flatten = (List.range 7680).map paddedSeedMask) (w : Nat) :
    unpack (combinationMask w bs) =
      ∑ k : Seed, if w.testBit k.val then seedVector k else 0 := by
  by_cases hw : w = 0
  · simp [combinationMask, hw, unpack_zero]
  rw [combinationMask, if_neg hw, selectBlocks_flatten w 0 bs hlen, hrows,
    List.range_eq_range', unpack_selectRows_range]
  simp only [Nat.zero_add]
  have hs : (∑ i ∈ Finset.range 7680, if w.testBit i then unpack (paddedSeedMask i) else 0) =
      ∑ i ∈ Finset.range 7620, if w.testBit i then unpack (paddedSeedMask i) else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by decide : 7620 ≤ 7680))
    intro i _ hi
    have hn : ¬ i < 7620 := by simpa using hi
    simp [paddedSeedMask, hn, unpack_zero]
  rw [hs, ← Fin.sum_univ_eq_sum_range
    (fun i => if w.testBit i then unpack (paddedSeedMask i) else 0) 7620]
  apply Finset.sum_congr rfl
  intro k _
  simp only [paddedSeedMask, if_pos k.isLt, unpack_rawSeedMask]

theorem row_of_masks (bs : List (List Nat))
    (hlen : ∀ b ∈ bs, b.length = 128)
    (hrows : bs.flatten = (List.range 7680).map paddedSeedMask)
    (s : Fin 2) (j : Fin 300)
    (h : packedColumn s j = combinationMask (combinationCode s j) bs) :
    columnVector s j = combinationVector s j := by
  rw [← unpack_packedColumn, h, unpack_combinationMask bs hlen hrows]
  rfl

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Parity
