module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.Checks

/-!
# Sound finite checks for the literal HS column orbit

Range checks keep numerical declarations small. The column checker compares
both bit planes with the original packed generator, so its interpretation is
an actual matrix transpose. A row product with that transpose is the required
column action. The inverse bridge uses the published LEFT-inverse contract.

Source: `Certificates/source/witnesses.json.gz` and the two accompanying
`source/README.md` files. The consumers are `ColumnChecks/Inverse.lean`,
`ColumnChecks/Transpose.lean`, and `ColumnChecks/Recursion.lean`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks

/-- Use division by a power, avoiding the recursive implementation of right shift. -/
def fastBit (a k : Nat) : Bool := decide (a / 2^k % 2 = 1)

theorem fastBit_eq (a k : Nat) : fastBit a k = a.testBit k :=
  Nat.testBit_eq_decide_div_mod_eq.symm

def fastProductFrom (a : Packed.Row) : Packed.Mat → Nat → Packed.Row
  | [], _ => (0,0)
  | b :: bs, k => Packed.Base.addRow
      (Packed.Base.addRow (if fastBit a.1 k then b else (0,0))
        (if fastBit a.2 k then Packed.Base.timesT b else (0,0)))
      (fastProductFrom a bs (k+1))

theorem fastProductFrom_eq (a : Packed.Row) (b : Packed.Mat) (k : Nat) :
    fastProductFrom a b k = Packed.rowProductFrom a b k := by
  induction b generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [fastProductFrom, Packed.rowProductFrom, fastBit_eq, ih]

def fastProduct (a : Packed.Row) (b : Packed.Mat) : Packed.Row :=
  match a with
  | (lo, hi) => fastProductFrom (lo, hi) b 0

theorem fastProduct_eq (a : Packed.Row) (b : Packed.Mat) :
    fastProduct a b = Packed.rowProduct a b := by
  cases a
  exact fastProductFrom_eq _ b 0

def checkRange (p : Nat → Bool) (start count : Nat) : Bool :=
  (List.range' start count).all p

theorem checkRange_get (p : Nat → Bool) (start count : Nat)
    (h : checkRange p start count = true) (i : Nat) (hlo : start ≤ i) (hhi : i < start + count) :
    p i = true := by
  apply List.all_eq_true.mp h i
  apply List.mem_range'.mpr
  refine ⟨i-start, by omega, ?_⟩
  omega

theorem checkRange_add (p : Nat → Bool) (start m n : Nat)
    (h : checkRange p start m = true) (g : checkRange p (start+m) n = true) :
    checkRange p start (m+n) = true := by
  unfold checkRange at *
  rw [← List.range'_append_1, List.all_append, h, g]
  rfl

def inverseStep (i : Nat) : Bool :=
  fastProduct (columnInverseRows.getD i (0,0)) columnRows == (2^i, 0)

theorem inverse_of_check (h : checkRange inverseStep 0 896 = true) :
    columnInverse * columnMatrix = 1 := by
  apply column_inverse_of_products
  intro i
  have hi : fastProduct (columnInverseRows.getD i.val (0,0)) columnRows = (2^i.val,0) :=
    eq_of_beq (checkRange_get _ _ _ h i.val (Nat.zero_le _) i.isLt)
  simpa only [fastProduct_eq] using hi

def checkColumnFrom : Packed.Mat → Packed.Row → Nat → Nat → Bool
  | [], _, _, _ => true
  | a :: rows, b, j, k =>
    ((fastBit a.1 j == fastBit b.1 k) && (fastBit a.2 j == fastBit b.2 k)) &&
      checkColumnFrom rows b j (k+1)

/-- Expose the literal row once, before the coordinate traversal. -/
def checkColumn (rows : Packed.Mat) (b : Packed.Row) (j k : Nat) : Bool :=
  match b with
  | (lo, hi) => checkColumnFrom rows (lo, hi) j k

theorem checkColumn_eq (rows : Packed.Mat) (b : Packed.Row) (j k : Nat) :
    checkColumn rows b j k = checkColumnFrom rows b j k := by
  cases b
  rfl

theorem checkColumn_get (rows : Packed.Mat) (b : Packed.Row) (j k : Nat)
    (h : checkColumn rows b j k = true) (i : Nat) (hi : i < rows.length) :
    Packed.decode (rows.getD i (0,0)) j = Packed.decode b (k+i) := by
  rw [checkColumn_eq] at h
  induction rows generalizing k i with
  | nil => simp at hi
  | cons a rows ih =>
    simp only [checkColumnFrom, fastBit_eq, Bool.and_eq_true] at h
    cases i with
    | zero =>
      have h₁ := eq_of_beq h.1.1
      have h₂ := eq_of_beq h.1.2
      simp only [List.getD_cons_zero, Nat.add_zero]
      unfold Packed.decode Packed.Base.entry
      simp only [Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
        h₁, h₂]
    | succ i =>
      simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using
        ih (k+1) h.2 i (Nat.lt_of_succ_lt_succ hi)

def transposeStep (rows cols : Packed.Mat) (j : Nat) : Bool :=
  checkColumn rows (cols.getD j (0,0)) j 0

theorem transpose_of_check (n : Nat) (rows cols : Packed.Mat) (hlen : rows.length = n)
    (h : checkRange (transposeStep rows cols) 0 n = true) :
    Packed.eval n cols = (Packed.eval n rows).transpose := by
  funext j i
  simp only [Packed.eval, Matrix.transpose_apply]
  simpa only [Nat.zero_add] using (checkColumn_get rows (cols.getD j.val (0,0)) j.val 0
    (checkRange_get _ _ _ h j.val (Nat.zero_le _) (by simpa only [Nat.zero_add] using j.isLt)) i.val
    (by simpa only [hlen] using i.isLt)).symm

def recursionStep (ta tb : Packed.Mat) (i : Nat) : Bool :=
  fastProduct (columnRows.getD (columnParents.getD i 0) (0,0))
    (if columnLetters.getD i 0 = 0 then ta else tb) == columnRows.getD (i+1) (0,0)

theorem mulVec_of_product (n : Nat) (g t : Packed.Mat) (v w : Packed.Row)
    (hlen : t.length = n) (ht : Packed.eval n t = (Packed.eval n g).transpose)
    (hp : Packed.rowProduct v t = w) :
    (fun j : Fin n => Packed.decode w j.val) =
      (Packed.eval n g).mulVec (fun j : Fin n => Packed.decode v j.val) := by
  funext j
  rw [← hp, Packed.decode_rowProduct _ _ n hlen]
  change (∑ k : Fin n, Packed.decode v k.val * Packed.eval n t k j) =
    ∑ k : Fin n, Packed.eval n g j k * Packed.decode v k.val
  rw [ht]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem recursion_of_check (ta tb : Packed.Mat) (hta : ta.length = 896) (htb : tb.length = 896)
    (ha : Packed.eval 896 ta = (Packed.eval 896 generatorRowsA).transpose)
    (hb : Packed.eval 896 tb = (Packed.eval 896 generatorRowsB).transpose)
    (h : checkRange (recursionStep ta tb) 0 895 = true) : ColumnRecursion := by
  intro i
  have heq := eq_of_beq (checkRange_get _ _ _ h i.val (Nat.zero_le _) i.isLt)
  change fastProduct _ _ = _ at heq
  rw [fastProduct_eq] at heq
  have hl : (if columnLetters.getD i.val 0 = 0 then ta else tb).length = 896 := by
    split <;> assumption
  have ht : Packed.eval 896 (if columnLetters.getD i.val 0 = 0 then ta else tb) =
      (Packed.eval 896 (packedLetter (columnLetters.getD i.val 0))).transpose := by
    unfold packedLetter
    split <;> assumption
  exact mulVec_of_product 896 (packedLetter (columnLetters.getD i.val 0))
    (if columnLetters.getD i.val 0 = 0 then ta else tb) _ _ hl ht heq

/-- Assemble a range from separately checked numerical equations. -/
theorem checkRange_one (p : Nat → Bool) (i : Nat) (h : p i = true) :
    checkRange p i 1 = true := by
  change (p i && true) = true
  simpa only [Bool.and_true] using h

/-- Resolve a literal row lookup separately from the product computation. -/
theorem inverseStep_of_row (i : Nat) (v : Packed.Row)
    (hv : columnInverseRows.getD i (0,0) = v)
    (hp : fastProduct v columnRows = (2^i,0)) : inverseStep i = true := by
  unfold inverseStep
  rw [hv, hp]
  exact beq_self_eq_true _

/-- A checked literal row is compared with every original generator row. -/
theorem transposeStep_of_row (rows cols : Packed.Mat) (i : Nat) (v : Packed.Row)
    (hv : cols.getD i (0,0) = v) (hp : checkColumn rows v i 0 = true) :
    transposeStep rows cols i = true := by
  unfold transposeStep
  rw [hv]
  exact hp

/-- Preserve the literal parent lookup, letter, and successor row while
checking the action on fully exposed numeric arguments. -/
theorem recursionStep_of_rows (ta tb : Packed.Mat) (i letter : Nat) (v w : Packed.Row)
    (hv : columnRows.getD (columnParents.getD i 0) (0,0) = v)
    (hl : columnLetters.getD i 0 = letter)
    (hw : columnRows.getD (i+1) (0,0) = w)
    (hp : fastProduct v (if letter = 0 then ta else tb) = w) :
    recursionStep ta tb i = true := by
  unfold recursionStep
  rw [hv, hl, hw, hp]
  exact beq_self_eq_true _

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks
