module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitData.Encoding

/-!
# Packed bit checks for reduced Lyons column bases

A certified pivot pattern supplies an increasing pivot map and a mask whose
base-eight digits at the pivots are seven. Masking each column then checks the
entire pivot minor at once; a remainder checks every entry before its pivot.
The mask may contain additional bits, since these only strengthen the check.
Pattern proofs are shared across all nodes having that pattern.

Canonical first columns are checked by three bit planes: a base-eight digit is
invalid precisely when its high bit and at least one of its lower bits are set.
A fixed mask selects the low bit of each of the 111 lanes. The length bound
excludes any hidden higher digits. These proofs use ordinary natural-number
bit operations and kernel reduction, without a native evaluator.

The data format comes from `Atlas111PlaneOrbitSource/GenerateOrbit.py`; the
remainder argument follows the analogous O'Nan certificate in
`ONan/ProjectiveOrder/CosetIndex/LowerBound/Certificate/Data/Basic.lean`.
No complete enumeration or closed full-data certificate is asserted here.
-/

public section

namespace Lyons.OrderCertificate.PlaneOrbitData

private theorem eight_pow (r : ℕ) : 8 ^ r = 2 ^ (3 * r) := by
  rw [pow_mul]
  rfl

private theorem digit_and (x y r : ℕ) : digit (x &&& y) r = digit x r &&& digit y r := by
  unfold digit
  rw [eight_pow, Nat.and_div_two_pow]
  exact Nat.and_mod_two_pow (n := 3)

private theorem digit_and_seven (x r : ℕ) : digit x r &&& 7 = digit x r := by
  have h := Nat.and_two_pow_sub_one_eq_mod (digit x r) 3
  simpa only [show 2 ^ 3 - 1 = 7 from rfl, show 2 ^ 3 = 8 from rfl,
    digit, Nat.mod_mod] using h

private theorem digit_pow (p r : ℕ) : digit (8 ^ p) r = if r = p then 1 else 0 := by
  unfold digit
  split_ifs with h
  · subst r
    simp
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [Nat.pow_div (Nat.le_of_lt hlt) (by decide)]
      apply Nat.mod_eq_zero_of_dvd
      exact Nat.div_pow_of_pos 8 (p-r) (by omega)
    · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_of_lt (by decide) hgt)]

private theorem digit_eq_zero_of_remainder {x p r : ℕ}
    (h : x % 8 ^ p = 0) (hr : r < p) : digit x r = 0 := by
  have hd : 8 ^ (r + 1) ∣ x :=
    (Nat.pow_dvd_pow 8 hr).trans (Nat.dvd_of_mod_eq_zero h)
  have he : 8 ∣ x / 8 ^ r := by
    apply Nat.dvd_div_of_mul_dvd
    simpa only [pow_succ] using hd
  exact Nat.mod_eq_zero_of_dvd he

/-- A reusable certified pivot pattern and a mask covering all pivot digits. -/
structure MaskPattern where
  pivot : Fin 7 → Fin 111
  increasing : StrictMono pivot
  mask : ℕ
  covers : ∀ i, digit mask (pivot i).val = 7

/-- Unrolled conjunction avoids a finite-quantifier loop in each node check. -/
@[expose] def allSeven (f : Fin 7 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6

private theorem allSeven_sound {f : Fin 7 → Bool} (h : allSeven f = true)
    (i : Fin 7) : f i = true := by
  simp only [allSeven, Bool.and_eq_true] at h
  fin_cases i <;> tauto

/-- Check seven pivot-minor masks and seven leading remainders. -/
@[expose] def checkMaskedReduced (rows : PackedRows) (p : MaskPattern) : Bool :=
  allSeven fun j => (rows j &&& p.mask == 8 ^ (p.pivot j).val) &&
    (rows j % 8 ^ (p.pivot j).val == 0)

/-- Packed shape checks imply the standard reduced-column-basis interface. -/
def reducedBasisOfMaskedCheck {rows : PackedRows} {p : MaskPattern}
    (h : checkMaskedReduced rows p = true) : Matrix.ReducedColumnBasis (columns rows) := by
  have hc : ∀ j, ((rows j &&& p.mask == 8 ^ (p.pivot j).val) &&
      (rows j % 8 ^ (p.pivot j).val == 0)) = true := allSeven_sound h
  refine ⟨p.pivot, p.increasing, ?_, ?_⟩
  · intro i j
    have hj := (Bool.and_eq_true _ _).mp (hc j)
    have hm : rows j &&& p.mask = 8 ^ (p.pivot j).val := by simpa using hj.1
    have hd := congrArg (fun x => digit x (p.pivot i).val) hm
    rw [digit_and, p.covers, digit_and_seven, digit_pow] at hd
    have he : (p.pivot i).val = (p.pivot j).val ↔ i = j := by
      constructor
      · exact fun h => p.increasing.injective (Fin.ext h)
      · exact fun h => congrArg (fun i => (p.pivot i).val) h
    simp only [he] at hd
    change (digit (rows j) (p.pivot i).val : ZMod 5) = _
    rw [hd]
    split_ifs <;> rfl
  · intro r j hr
    have hj := (Bool.and_eq_true _ _).mp (hc j)
    have hz : rows j % 8 ^ (p.pivot j).val = 0 := by simpa using hj.2
    change (digit (rows j) r.val : ZMod 5) = 0
    rw [digit_eq_zero_of_remainder hz hr]
    rfl

private theorem testBit_digit (x r t : ℕ) (ht : t < 3) :
    (digit x r).testBit t = x.testBit (3*r+t) := by
  unfold digit
  rw [eight_pow]
  change (x / 2 ^ (3*r) % 2 ^ 3).testBit t = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [ht, decide_true, Bool.true_and, Nat.add_comm t]

private theorem small_digit (d : ℕ) (hd : d < 8)
    (h : (d.testBit 2 && (d.testBit 0 || d.testBit 1)) = false) : d < 5 := by
  have hf : ∀ d : Fin 8,
      (d.val.testBit 2 && (d.val.testBit 0 || d.val.testBit 1)) = false → d.val < 5 := by
    decide +kernel
  exact hf ⟨d, hd⟩ h

/-- One low bit in each of the 111 base-eight lanes. -/
@[expose] def lowMask : ℕ := 2499715114037727913568573973848710131832193635306528498772309264468517713370715340826872202312061513

private theorem lowMask_covers : ∀ r : Fin 111, lowMask.testBit (3*r.val) = true := by
  decide +kernel

/-- Check canonical GF(5) digits simultaneously in all 111 lanes. -/
@[expose] def checkMaskedValidColumn (x : ℕ) : Bool :=
  (x < 8 ^ 111) && (((x >>> 2) &&& (x ||| (x >>> 1))) &&& lowMask == 0)

/-- No modular aliases or hidden digits survive the bit-plane check. -/
theorem validColumnOfMaskedCheck {x : ℕ} (h : checkMaskedValidColumn x = true) :
    ValidColumn x := by
  simp only [checkMaskedValidColumn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  intro r
  have hb := congrArg (fun z => z.testBit (3*r.val)) h.2
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight,
    lowMask_covers, Bool.and_true, Nat.zero_testBit] at hb
  have he (t : ℕ) (ht : t < 3) :
      x.testBit (t + 3*r.val) = (digit x r.val).testBit t := by
    rw [testBit_digit x r.val t ht, Nat.add_comm]
  rw [he 2 (by decide), he 1 (by decide)] at hb
  have h0 := testBit_digit x r.val 0 (by decide)
  simp only [Nat.add_zero] at h0
  rw [← h0] at hb
  exact small_digit _ (Nat.mod_lt _ (by decide)) hb

/-- The independent shape and first-column checks needed for sorted separation. -/
@[expose] def checkMaskedNode (rows : PackedRows) (p : MaskPattern) : Bool :=
  checkMaskedValidColumn (rows 0) && checkMaskedReduced rows p

theorem validColumn_of_maskedNode {rows : PackedRows} {p : MaskPattern}
    (h : checkMaskedNode rows p = true) : ValidColumn (rows 0) :=
  validColumnOfMaskedCheck ((Bool.and_eq_true _ _).mp h).1

def reducedBasis_of_maskedNode {rows : PackedRows} {p : MaskPattern}
    (h : checkMaskedNode rows p = true) : Matrix.ReducedColumnBasis (columns rows) :=
  reducedBasisOfMaskedCheck ((Bool.and_eq_true _ _).mp h).2

/-- A block of checked nodes, stated over natural intervals for shard assembly. -/
@[expose] def MaskedCheckedOn (lo hi : ℕ) (rows : ℕ → PackedRows) (pattern : ℕ → MaskPattern) : Prop :=
  ∀ i, lo ≤ i → i < hi → checkMaskedNode (rows i) (pattern i) = true

/-- A finite closed check supplies one interval in a larger certificate. -/
theorem maskedCheckedOn_of_fin {lo n : ℕ} {rows : ℕ → PackedRows}
    {pattern : ℕ → MaskPattern}
    (h : ∀ i : Fin n, checkMaskedNode (rows (lo + i.val)) (pattern (lo + i.val)) = true) :
    MaskedCheckedOn lo (lo + n) rows pattern := by
  intro i hlo hhi
  have he : lo + (i - lo) = i := by omega
  simpa only [he] using h ⟨i - lo, by omega⟩

/-- Combine separately checked adjacent intervals without re-evaluating their data. -/
theorem maskedCheckedOn_append {lo mid hi : ℕ} {rows : ℕ → PackedRows}
    {pattern : ℕ → MaskPattern}
    (hl : MaskedCheckedOn lo mid rows pattern)
    (hr : MaskedCheckedOn mid hi rows pattern) : MaskedCheckedOn lo hi rows pattern := by
  intro i hlo hhi
  by_cases h : i < mid
  · exact hl i hlo h
  · exact hr i (by omega) hhi

/-- Extract every reduced basis after the last shard has been assembled. -/
def reducedBasis_of_maskedCheckedOn {n : ℕ} {rows : ℕ → PackedRows}
    {pattern : ℕ → MaskPattern} (h : MaskedCheckedOn 0 n rows pattern) (i : Fin n) :
    Matrix.ReducedColumnBasis (columns (rows i.val)) :=
  reducedBasis_of_maskedNode (h i.val (Nat.zero_le _) i.isLt)

/-- Closed shape checks and exact adjacent sorting certify distinct matrices. -/
theorem columns_injective_of_maskedCheckedOn {n : ℕ} (rows : ℕ → PackedRows)
    (pattern : ℕ → MaskPattern) (order : Fin (n + 1) → Fin (n + 1))
    (h : MaskedCheckedOn 0 (n + 1) rows pattern)
    (hsort : ∀ i : Fin n, rows (order i.castSucc).val 0 < rows (order i.succ).val 0) :
    Function.Injective (fun i : Fin (n + 1) => columns (rows i.val)) := by
  exact columns_injective_of_adjacent _ order
    (fun i => validColumn_of_maskedNode (h i.val (Nat.zero_le _) i.isLt)) hsort

end Lyons.OrderCertificate.PlaneOrbitData
