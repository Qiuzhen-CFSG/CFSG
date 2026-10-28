module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.Setup
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Packed

/-!
# Balanced certificates for the literal column orbit

Checked table views replace repeated lookup in large source arrays. Each node
certifies its left length and the corresponding power of two. The XOR append
identity proves product soundness; bit checks prove literal transposition.
Well-founded induction on prepended source words identifies the column orbit.

Source: ATLAS HSG1-f2r1000B0 and `Binary/source/density1000.json`.
See `ColumnSpan/source/README.md` for conventions, attribution and measurements.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan
open RowArithmetic

inductive Table (α : Type) where
  | leaf (rows : List α)
  | node (leftSize leftPower : Nat) (left right : Table α)

def Table.rows {α : Type} : Table α → List α
  | .leaf rs => rs
  | .node _ _ l r => l.rows ++ r.rows

def Table.valid {α : Type} : Table α → Bool
  | .leaf _ => true
  | .node n p l r => decide (n = l.rows.length) && decide (p = 2 ^ n) && l.valid && r.valid

def Table.get {α : Type} [Inhabited α] (i : Nat) : Table α → α
  | .leaf rs => rs[i]!
  | .node n _ l r => if i < n then l.get i else r.get (i-n)

theorem Table.get_eq {α : Type} [Inhabited α] (t : Table α) (ht : t.valid = true) (i : Nat) :
    t.get i = t.rows[i]! := by
  induction t generalizing i with
  | leaf rs => rfl
  | node n p l r il ir =>
    simp only [Table.valid, Bool.and_eq_true, decide_eq_true_eq] at ht
    simp only [Table.get, Table.rows]
    by_cases hi : i < n
    · rw [if_pos hi, il ht.1.2]
      simp only [List.getElem!_eq_getElem?_getD,
        List.getElem?_append_left (show i < l.rows.length by omega)]
    · rw [if_neg hi, ir ht.2, ht.1.1.1]
      simp only [List.getElem!_eq_getElem?_getD,
        List.getElem?_append_right (show l.rows.length ≤ i by omega)]

theorem Table.get_eq_array {α : Type} [Inhabited α] (t : Table α) (a : Array α)
    (ht : t.valid = true) (ha : t.rows = a.toList) (i : Nat) : t.get i = a[i]! := by
  rw [t.get_eq ht, ha, Array.getElem!_toList]

abbrev RowTree := Table Nat

def RowTree.product (x : Nat) : RowTree → Nat
  | .leaf rs => combine rs x
  | .node _ p l r => RowTree.product x l ^^^ RowTree.product (x / p) r

theorem RowTree.product_eq (t : RowTree) (h : t.valid = true) (x : Nat) :
    t.product x = combine t.rows x := by
  induction t generalizing x with
  | leaf rs => rfl
  | node n p l r il ir =>
    simp only [Table.valid, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RowTree.product, Table.rows, combine_append, Nat.shiftRight_eq_div_pow]
    rw [h.1.1.2, il h.1.2, ir h.2, h.1.1.1]

def On (P : Nat → Prop) (lo hi : Nat) : Prop := ∀ i, lo ≤ i → i < hi → P i

theorem On.append {P : Nat → Prop} {lo mid hi : Nat}
    (h₁ : On P lo mid) (h₂ : On P mid hi) : On P lo hi := by
  intro i hlo hhi
  by_cases hm : i < mid
  · exact h₁ i hlo hm
  · exact h₂ i (by omega) hhi

def listMatch (power x : Nat) : List Nat → Bool
  | [] => true
  | r :: rs => (decide (r / power % 2 = 1) == x.testBit 0) && listMatch power (x >>> 1) rs

theorem listMatch_append (p x : Nat) (rs ss : List Nat) :
    listMatch p x (rs ++ ss) = (listMatch p x rs && listMatch p (x >>> rs.length) ss) := by
  induction rs generalizing x with
  | nil => simp [listMatch]
  | cons r rs ih =>
    simp only [List.cons_append, listMatch, ih, List.length_cons, Bool.and_assoc,
      ← Nat.shiftRight_add, Nat.add_comm 1]

theorem listMatch_get (rs : List Nat) (j x : Nat) (h : listMatch (2 ^ j) x rs = true)
    (i : Nat) (hi : i < rs.length) : rs[i]!.testBit j = x.testBit i := by
  induction rs generalizing x i with
  | nil => simp at hi
  | cons r rs ih =>
    simp only [listMatch, Bool.and_eq_true, beq_iff_eq,
      ← Nat.testBit_eq_decide_div_mod_eq] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      simpa only [List.getElem!_cons_succ, Nat.testBit_shiftRight, Nat.add_comm 1] using
        ih (x >>> 1) h.2 i (by simpa using hi)

def RowTree.columnMatch (power x : Nat) : RowTree → Bool
  | .leaf rs => listMatch power x rs
  | .node _ p l r => RowTree.columnMatch power x l && RowTree.columnMatch power (x / p) r

theorem RowTree.columnMatch_eq (t : RowTree) (h : t.valid = true) (p x : Nat) :
    t.columnMatch p x = listMatch p x t.rows := by
  induction t generalizing x with
  | leaf rs => rfl
  | node n q l r il ir =>
    simp only [Table.valid, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RowTree.columnMatch, Table.rows, listMatch_append, Nat.shiftRight_eq_div_pow]
    rw [h.1.1.2, il h.1.2, ir h.2, h.1.1.1]

theorem transpose_of_checks (t s : RowTree) (a : Array Nat) (n : Nat)
    (ht : t.valid = true) (hs : s.valid = true) (ha : s.rows = a.toList)
    (hlen : t.rows.length = n)
    (h : On (fun j => t.columnMatch (2 ^ j) (s.get j) = true) 0 n) :
    matrix n n t.rows = (Thompson.BinaryMatrix.decode n a).transpose := by
  funext i j
  have hh := h j.val (Nat.zero_le _) j.isLt
  change t.columnMatch (2 ^ j.val) (s.get j.val) = true at hh
  rw [t.columnMatch_eq ht, s.get_eq_array a hs ha] at hh
  have he := listMatch_get t.rows j.val a[j.val]! hh i.val (by rw [hlen]; exact i.isLt)
  simp only [matrix, Thompson.BinaryMatrix.decode, Matrix.transpose_apply,
    Thompson.BinaryMatrix.bit, he]

theorem inverse_of_checks (t s : RowTree) (a b : Array Nat) (n : Nat)
    (ht : t.valid = true) (hs : s.valid = true) (ha : t.rows = a.toList)
    (hb : s.rows = b.toList) (hlen : a.size = n)
    (h : On (fun i => decide (t.product (s.get i) = 2 ^ i) = true) 0 n) :
    Thompson.BinaryMatrix.decode n b * Thompson.BinaryMatrix.decode n a = 1 := by
  funext i
  apply decode_product_one_row n b a i hlen
  rw [← ha, ← t.product_eq ht, ← s.get_eq_array b hs hb]
  exact of_decide_eq_true (h i.val (Nat.zero_le _) i.isLt)

theorem vecMul_of_product (t : RowTree) (n : Nat) (ht : t.valid = true)
    (hlen : t.rows.length = n) (x y : Nat) (h : t.product x = y) :
    Matrix.vecMul (vector n x) (matrix n n t.rows) = vector n y := by
  rw [← vector_combine t.rows n n hlen x, ← t.product_eq ht, h]

def OrbitStep (a b cols : RowTree) (words : Table (List Bool)) (i : Nat) : Prop :=
  ∃ p c, p < i ∧ words.get i = c :: words.get p ∧
    (if c then b else a).product (cols.get p) = cols.get i

theorem orbits_of_steps (a b cols : RowTree) (words : Table (List Bool))
    (ha : a.valid = true) (hb : b.valid = true) (hc : cols.valid = true) (hw : words.valid = true)
    (hca : cols.rows = Data.columnRows.toList) (hwa : words.rows = Data.columnWords.toList)
    (hla : a.rows.length = 1000) (hlb : b.rows.length = 1000)
    (hga : matrix 1000 1000 a.rows = (generator false).transpose)
    (hgb : matrix 1000 1000 b.rows = (generator true).transpose)
    (h : On (OrbitStep a b cols words) 1 1000) :
    ∀ i : Fin 1000, columnOrbit i = vector 1000 Data.columnRows[i.val]! := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hz : i = 0
    · subst i
      have hw0 : Data.columnWords[0]! = [] := by decide +kernel
      have hx0 : Data.columnRows[0]! = Data.image := by decide +kernel
      change (wordMatrix Data.columnWords[0]!).mulVec imageVector = vector 1000 Data.columnRows[0]!
      rw [hw0, wordMatrix, Matrix.one_mulVec, hx0]
      rfl
    · have hn : 1 ≤ i.val := by
        have : i.val ≠ 0 := fun he => hz (Fin.ext he)
        omega
      obtain ⟨p, c, hp, hword, hprod⟩ := h i.val hn i.isLt
      simp only [words.get_eq_array Data.columnWords hw hwa] at hword
      simp only [cols.get_eq_array Data.columnRows hc hca] at hprod
      let p' : Fin 1000 := ⟨p, lt_trans hp i.isLt⟩
      have hvec := ih p' hp
      have haction : (generator c).mulVec (vector 1000 Data.columnRows[p]!) =
          vector 1000 Data.columnRows[i.val]! := by
        cases c with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hprod
          have hv := vecMul_of_product a 1000 ha hla _ _ hprod
          rw [hga, Matrix.vecMul_transpose] at hv
          exact hv
        | true =>
          simp only [↓reduceIte] at hprod
          have hv := vecMul_of_product b 1000 hb hlb _ _ hprod
          rw [hgb, Matrix.vecMul_transpose] at hv
          exact hv
      change (wordMatrix Data.columnWords[i.val]!).mulVec imageVector = _
      rw [hword, wordMatrix, ← Matrix.mulVec_mulVec]
      change (generator c).mulVec (columnOrbit p') = _
      rw [hvec]
      exact haction

def caseChecks {α : Type} (f : Nat → α → Bool) (lo : Nat) : List α → Bool
  | [] => true
  | x :: xs => f lo x && caseChecks f (lo+1) xs

theorem on_of_caseChecks {α : Type} (f : Nat → α → Bool) (lo : Nat) (xs : List α)
    (h : caseChecks f lo xs = true) : On (fun i => ∃ x, f i x = true) lo (lo+xs.length) := by
  induction xs generalizing lo with
  | nil => intro i hlo hhi; simp only [List.length_nil] at hhi; omega
  | cons x xs ih =>
    simp only [caseChecks, Bool.and_eq_true] at h
    intro i hlo hhi
    by_cases he : i = lo
    · subst i; exact ⟨x, h.1⟩
    · exact ih (lo+1) h.2 i (by omega) (by simp only [List.length_cons] at hhi; omega)

def inverseCase (t s : RowTree) (i x : Nat) : Bool :=
  decide (s.get i = x) && decide (t.product x = 2 ^ i)

theorem inverseOn_of_cases (t s : RowTree) (lo : Nat) (xs : List Nat)
    (h : caseChecks (inverseCase t s) lo xs = true) :
    On (fun i => decide (t.product (s.get i) = 2 ^ i) = true) lo (lo+xs.length) := by
  intro i hlo hhi
  obtain ⟨x, hx⟩ := on_of_caseChecks _ _ _ h i hlo hhi
  simp only [inverseCase, Bool.and_eq_true, decide_eq_true_eq] at hx
  simp only [hx.1, hx.2, decide_true]

def transposeCase (t s : RowTree) (i : Nat) (x : Nat × Nat) : Bool :=
  decide (x.1 = 2 ^ i) && decide (s.get i = x.2) && t.columnMatch x.1 x.2

theorem transposeOn_of_cases (t s : RowTree) (lo : Nat) (xs : List (Nat × Nat))
    (h : caseChecks (transposeCase t s) lo xs = true) :
    On (fun i => t.columnMatch (2 ^ i) (s.get i) = true) lo (lo+xs.length) := by
  intro i hlo hhi
  obtain ⟨x, hx⟩ := on_of_caseChecks _ _ _ h i hlo hhi
  simp only [transposeCase, Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [hx.1.2, ← hx.1.1]
  exact hx.2

structure Step where
  parent : Nat
  letter : Bool
  input : Nat
  output : Nat

def orbitCase (a b cols : RowTree) (words : Table (List Bool)) (i : Nat) (s : Step) : Bool :=
  decide (cols.get s.parent = s.input) && decide (cols.get i = s.output) &&
  decide (s.parent < i) && decide (words.get i = s.letter :: words.get s.parent) &&
  decide ((if s.letter then b else a).product s.input = s.output)

theorem orbitOn_of_cases (a b cols : RowTree) (words : Table (List Bool))
    (lo : Nat) (xs : List Step)
    (h : caseChecks (orbitCase a b cols words) lo xs = true) :
    On (OrbitStep a b cols words) lo (lo+xs.length) := by
  intro i hlo hhi
  obtain ⟨s, hs⟩ := on_of_caseChecks _ _ _ h i hlo hhi
  simp only [orbitCase, Bool.and_eq_true, decide_eq_true_eq] at hs
  rcases hs with ⟨⟨⟨⟨hx, hy⟩, hlt⟩, hw⟩, hv⟩
  exact ⟨s.parent, s.letter, hlt, hw, by rw [hx, hy]; exact hv⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan
