module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.LiteralArithmetic

/-!
# Checked transposition of packed row tables

The rows are stored in a balanced tree of short lists. A checked scale at each
branch records the size of its left block. The verifier splits a proposed
column at these scales and checks its bits by division and remainder. Its
soundness identifies the result with `transposeRow`, and checked record maps
cover every column and compare the entire fixed candidate table.

Both degree-1242 transpose certificates consume these lemmas. Original ATLAS
attribution and conventions: `Degrees12421792/source/README.md`; application:
James, J. Algebra 27 (1973), 57–111. No external calculation is trusted.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.FirstTranspose

/-- Column extraction by direct list recursion and primitive natural arithmetic. -/
def extract (p : ℕ) : List ℕ → ℕ :=
  List.rec 0 (fun a _ r => a / p % 2 + 2 * r)

private theorem bit_digit (a p r : ℕ) :
    Nat.bit (decide (a / p % 2 = 1)) r = a / p % 2 + 2 * r := by
  rcases Nat.mod_two_eq_zero_or_one (a / p) with h | h <;>
    simp [h, Nat.bit, Nat.add_comm]

theorem extract_eq (xs : List ℕ) (j : ℕ) :
    extract (2 ^ j) xs = transposeRow xs j := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change a / 2 ^ j % 2 + 2 * extract (2 ^ j) as = _
    rw [ih, transposeRow, Nat.testBit_eq_decide_div_mod_eq, bit_digit]

theorem extract_append (p : ℕ) (xs ys : List ℕ) :
    extract p (xs ++ ys) = extract p xs + 2 ^ xs.length * extract p ys := by
  induction xs with
  | nil => simp [extract]
  | cons a as ih =>
    change a / p % 2 + 2 * extract p (as ++ ys) =
      (a / p % 2 + 2 * extract p as) + 2 ^ (as.length + 1) * extract p ys
    rw [ih, pow_succ]
    ring

inductive RowTree where
  | leaf : List ℕ → RowTree
  | branch : ℕ → RowTree → RowTree → RowTree

def RowTree.rows : RowTree → List ℕ :=
  RowTree.rec id (fun _ _ _ l r => l ++ r)

def RowTree.length : RowTree → ℕ :=
  RowTree.rec List.length (fun _ _ _ l r => l + r)

def RowTree.eval (p : ℕ) : RowTree → ℕ :=
  RowTree.rec (extract p) (fun w _ _ a b => a + w * b)

def RowTree.valid : RowTree → Bool :=
  RowTree.rec (fun _ => true) (fun w l _ a b => (w == 2 ^ l.length) && a && b)

theorem RowTree.rows_length (t : RowTree) : t.rows.length = t.length := by
  induction t with
  | leaf a => rfl
  | branch w l r hl hr =>
    change (l.rows ++ r.rows).length = l.length + r.length
    rw [List.length_append, hl, hr]

theorem RowTree.eval_eq (t : RowTree) (p : ℕ) (ht : t.valid = true) :
    t.eval p = extract p t.rows := by
  induction t with
  | leaf a => rfl
  | branch w l r hl hr =>
    change ((w == 2 ^ l.length) && l.valid && r.valid) = true at ht
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    change l.eval p + w * r.eval p = extract p (l.rows ++ r.rows)
    rw [extract_append, hl ht.1.2, hr ht.2, rows_length, ht.1.1]

def checkExtract (p : ℕ) : List ℕ → ℕ → Bool :=
  List.rec (fun q => Nat.beq q 0)
    (fun a _ rec q => Bool.and (Nat.beq (Nat.mod (Nat.div a p) 2) (Nat.mod q 2))
      (rec (Nat.div q 2)))

theorem checkExtract_sound (p : ℕ) (xs : List ℕ) (q : ℕ)
    (h : checkExtract p xs q = true) : extract p xs = q := by
  induction xs generalizing q with
  | nil =>
    have hq : q = 0 := by simpa only [checkExtract, Nat.beq_eq] using h
    exact hq.symm
  | cons a as ih =>
    change Bool.and (Nat.beq (a / p % 2) (q % 2)) (checkExtract p as (q / 2)) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    change a / p % 2 + 2 * extract p as = q
    rw [h.1, ih _ h.2, Nat.mod_add_div]

def RowTree.verify (p : ℕ) : RowTree → ℕ → Bool :=
  RowTree.rec (checkExtract p)
    (fun w _ _ l r q => Bool.and (l (Nat.mod q w)) (r (Nat.div q w)))

theorem RowTree.verify_sound (t : RowTree) (p q : ℕ)
    (h : t.verify p q = true) : t.eval p = q := by
  induction t generalizing q with
  | leaf xs => exact checkExtract_sound p xs q h
  | branch w l r hl hr =>
    change (l.verify p (q % w) && r.verify p (q / w)) = true at h
    simp only [Bool.and_eq_true] at h
    change l.eval p + w * r.eval p = q
    rw [hl _ h.1, hr _ h.2, Nat.mod_add_div]

structure Record where
  column : ℕ
  power : ℕ
  value : ℕ

def rowCheck (xs : RowTree) (c : Record) : Bool :=
  Bool.and (Nat.beq c.power (Nat.pow 2 c.column)) (xs.verify c.power c.value)

theorem rowCheck_sound (xs : RowTree) (c : Record) (ht : xs.valid = true) (h : rowCheck xs c = true) :
    transposeRow xs.rows c.column = c.value := by
  simp only [rowCheck, Bool.and_eq_true, Nat.beq_eq] at h
  have hv := RowTree.verify_sound xs c.power c.value h.2
  rw [h.1, RowTree.eval_eq xs _ ht] at hv
  change extract (2 ^ c.column) xs.rows = c.value at hv
  rw [extract_eq] at hv
  exact hv

/-- Both the index coverage and the entire candidate table are checked. -/
theorem checked_of_records (n : ℕ) (xs : RowTree) (ys : List ℕ) (cs : List Record)
    (ht : xs.valid = true)
    (hcover : cs.map Record.column = List.range n)
    (hvalues : cs.map Record.value = ys)
    (hcheck : cs.all (rowCheck xs) = true) (i : Fin n) :
    transposeRow xs.rows i.val = entry ys i.val := by
  have hm : (cs.map Record.column).map (transposeRow xs.rows) = cs.map Record.value := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    exact rowCheck_sound xs c ht (List.all_eq_true.mp hcheck c hc)
  rw [hcover, hvalues] at hm
  have hi := congrArg (fun zs : List ℕ => entry zs i.val) hm
  simpa only [entry, List.getElem?_map, List.getElem?_range i.isLt,
    Option.map_some, Option.getD_some] using hi

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.FirstTranspose
