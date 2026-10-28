module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Operators
public import Theory.LinearAlgebra.PackedBinaryRows
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Sound packed arithmetic for the fixed Hall--Janko operators

Bit j of a natural number represents coordinate j over F₂. XOR therefore
represents vector addition. The interval checker from `PackedBinaryRows`
represents the sum of precisely the selected input rows, so `decode_action`
identifies its result with the unchanged `Presentation.operator`.

The word and relation bridges preserve successive right multiplication and
the actual seed, including the empty word. The generation bridge reduces the
full word-span obligation to checked inverse rows. These are soundness lemmas;
they do not assert that any numerical generation or relation witness passes.

Source: `Presentation/source/README.md` and its unchanged discovery data.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates
open PackedBinaryRows

def bit (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0

def decode (x : ℕ) : Coordinates := fun j => bit x j.val

lemma bit_xor (x y j : ℕ) : bit (x ^^^ y) j = bit x j + bit y j := by
  simp only [bit, Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

lemma bit_zero (j : ℕ) : bit 0 j = 0 := by simp [bit]

lemma decode_zero : decode 0 = 0 := by ext j; exact bit_zero _

lemma decode_xor (x y : ℕ) : decode (x ^^^ y) = decode x + decode y := by
  ext j; exact bit_xor _ _ _

lemma bit_rowRange (x : ℕ) (r : ℕ → ℕ) (start n j : ℕ) :
    bit (rowRange x r start n) j =
      ∑ i : Fin n, bit x (start + i.val) * bit (r (start + i.val)) j := by
  induction n with
  | zero => simp [rowRange, bit_zero]
  | succ n ih =>
    rw [rowRange, bit_xor, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    congr 1
    cases h : x.testBit (start + n) <;> simp [bit, h]

def action (k : Fin 9) (x : ℕ) : ℕ := rowRange x (fun i => (rows k)[i]!) 0 1008

lemma decode_action (k : Fin 9) (x : ℕ) :
    decode (action k x) = operator k (decode x) := by
  ext j
  simp only [operator, AddMonoidHom.coe_mk, ZeroHom.coe_mk, decode]
  rw [action, bit_rowRange]
  simp only [Nat.zero_add, entry, bit]

/-- A checked prefix and one new action certify the appended word. -/
lemma runWord_append_step {w : List (Fin 9)} {k : Fin 9} {x y : ℕ}
    (hw : runWord action 1 w = x) (hy : action k x = y) :
    runWord action 1 (w ++ [k]) = y := by
  simp only [runWord, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
  rw [hw, hy]

lemma decode_seed : decode 1 = seed := by
  ext j
  change (if (1 : ℕ).testBit j.val then (1 : ZMod 2) else 0) =
    if j = 0 then 1 else 0
  rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
  simp only [Fin.ext_iff, Fin.val_zero]
  by_cases hj : j.val = 0
  · simp [hj]
  · simp [hj, Ne.symm hj]

lemma decode_runWord (x : ℕ) (w : List (Fin 9)) :
    decode (runWord action x w) = runWord (fun k => operator k) (decode x) w := by
  induction w generalizing x with
  | nil => rfl
  | cons k w ih =>
    simp only [runWord, List.foldl_cons] at *
    rw [ih, decode_action]

lemma decode_runCode (i j : Fin 9) (n : ℕ) :
    decode (runCode action 1 i j n) = runCode (fun k => operator k) seed i j n := by
  simp only [runCode, decode_runWord, decode_seed]

def xorList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x ^^^ xorList xs

lemma decode_xorList (xs : List ℕ) :
    decode (xorList xs) = (xs.map decode).sum := by
  induction xs with
  | nil => exact decode_zero
  | cons x xs ih => simp only [xorList, decode_xor, ih, List.map_cons, List.sum_cons]

def relation (r : Certificate.Relation) : ℕ :=
  xorList (r.terms.map (runCode action 1 r.first r.second))

lemma decode_relation (r : Certificate.Relation) :
    decode (relation r) = runRelation (fun k => operator k) seed r := by
  simp only [relation, decode_xorList, List.map_map, Function.comp_def,
    decode_runCode, runRelation]

def wordSums : AddSubmonoid Coordinates where
  carrier := {v | ∃ ws : List (List (Fin 9)),
    (ws.map (runWord (fun k => operator k) seed)).sum = v}
  zero_mem' := ⟨[], rfl⟩
  add_mem' := by
    rintro v u ⟨vs, rfl⟩ ⟨us, rfl⟩
    exact ⟨vs ++ us, by simp only [List.map_append, List.sum_append]⟩

lemma word_mem (w : List (Fin 9)) :
    runWord (fun k => operator k) seed w ∈ wordSums := by
  exact ⟨[w], by simp only [List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]⟩

lemma decode_word_mem (w : List (Fin 9)) : decode (runWord action 1 w) ∈ wordSums := by
  rw [decode_runWord, decode_seed]
  exact word_mem w

lemma decode_unit (i : Fin 1008) : decode (2 ^ i.val) = Pi.single i 1 := by
  ext j
  simp only [decode, bit, Nat.testBit_two_pow, Pi.single_apply,
    decide_eq_true_eq, Fin.ext_iff]
  simp only [eq_comm]

lemma wordSpan_of_units (h : ∀ i : Fin 1008, decode (2 ^ i.val) ∈ wordSums) :
    CoordinateWordSpan := by
  intro v
  change v ∈ wordSums
  apply Pi.single_induction (fun v : Coordinates => v ∈ wordSums) v
    wordSums.zero_mem (fun _ _ => wordSums.add_mem)
  intro i a
  have binary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have ha : a = 0 ∨ a = 1 := binary a
  rcases ha with rfl | rfl
  · simpa only [Pi.single_zero] using wordSums.zero_mem
  · rw [← decode_unit]
    exact h i

lemma decode_rowRange_mem (x : ℕ) (r : ℕ → ℕ) (start n : ℕ)
    (h : ∀ i, start ≤ i → i < start + n → decode (r i) ∈ wordSums) :
    decode (rowRange x r start n) ∈ wordSums := by
  induction n with
  | zero => simpa only [rowRange, decode_zero] using wordSums.zero_mem
  | succ n ih =>
    rw [rowRange, decode_xor]
    apply wordSums.add_mem (ih (fun i h0 hi => h i h0 (by omega)))
    split_ifs
    · exact h _ (by omega) (by omega)
    · rw [decode_zero]; exact wordSums.zero_mem

/-- Append another independently evaluated interval. -/
lemma rowRange_extend {x : ℕ} {r : ℕ → ℕ} {start n a b c : ℕ}
    (ha : rowRange x r 0 start = a) (hb : rowRange x r start n = b)
    (hc : a ^^^ b = c) : rowRange x r 0 (start + n) = c := by
  rw [rowRange_add, Nat.zero_add, ha, hb, hc]

/-- Inverse-row witnesses reduce spanning to binary row arithmetic. -/
lemma wordSpan_of_inverse (r : ℕ → ℕ) (coeff : Fin 1008 → ℕ)
    (hr : ∀ i : Fin 1008, decode (r i.val) ∈ wordSums)
    (hinv : ∀ i : Fin 1008, rowRange (coeff i) r 0 1008 = 2 ^ i.val) :
    CoordinateWordSpan := by
  apply wordSpan_of_units
  intro i
  rw [← hinv i]
  apply decode_rowRange_mem
  intro j _ hj
  exact hr ⟨j, hj⟩

lemma coordinateRelations_of_checks
    (h : ∀ r ∈ Certificate.relations, relation r = 0) : CoordinateRelations := by
  intro r hr
  rw [← decode_relation, h r hr, decode_zero]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates
