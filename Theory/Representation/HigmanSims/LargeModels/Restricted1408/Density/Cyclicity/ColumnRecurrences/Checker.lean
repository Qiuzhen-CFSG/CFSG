module

public import Theory.LinearAlgebra.PackedBinaryRows

/-!
# Checkers for column-orbit certificates

A column is packed by scanning the literal rows. Its bit theorem fixes the
transpose convention. Product checks use the existing ordinary XOR row product.
The separate layout and input checks connect proposed steps to the published
orbit arrays; ordered parent references allow a linear scan of the input rows.
See `source/README.md` for the concrete HS application and source conventions.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

def column (j : Nat) : List Nat → Nat
  | [] => 0
  | r :: rs => 2 * column j rs + if r.testBit j then 1 else 0

lemma column_bit (j : Nat) (rs : List Nat) (i : Nat) :
    (column j rs).testBit i = rs[i]!.testBit j := by
  induction rs generalizing i with
  | nil => simp [column]
  | cons r rs ih =>
    have hb : (if r.testBit j then 1 else 0) < 2^1 := by split <;> decide
    rw [column, show 2 = 2^1 from rfl, Nat.testBit_two_pow_mul_add _ hb]
    cases i with
    | zero => cases h : r.testBit j <;> simp [h]
    | succ i => simpa [List.getElem!_cons_succ] using ih i

def columnsCheck (rs : List Nat) (start : Nat) : List Nat → Bool
  | [] => true
  | c :: cs => (column start rs == c) && columnsCheck rs (start+1) cs

lemma columnsCheck_append (rs cs ds : List Nat) (start : Nat) :
    columnsCheck rs start (cs ++ ds) =
      (columnsCheck rs start cs && columnsCheck rs (start + cs.length) ds) := by
  induction cs generalizing start with
  | nil => simp [columnsCheck]
  | cons c cs ih =>
    simp only [List.cons_append, columnsCheck, ih, List.length_cons,
      Bool.and_assoc, Nat.add_assoc, Nat.add_comm 1]

lemma columnsCheck_sound (rs cs : List Nat) (start : Nat)
    (h : columnsCheck rs start cs = true) (i : Nat) (hi : i < cs.length) :
    column (start+i) rs = cs[i]! := by
  induction cs generalizing start i with
  | nil => simp at hi
  | cons c cs ih =>
    simp only [columnsCheck, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa only [Nat.add_zero, List.getElem!_cons_zero] using h.1
    | succ i =>
      simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using
        ih (start+1) h.2 i (Nat.lt_of_succ_lt_succ hi)

/-- One proposed step, with the packed input stored explicitly for arithmetic checks. -/
structure Step where
  parent : Nat
  input : Nat
  choice : Bool
  output : Nat
  deriving Inhabited

def productsCheck (a b : List Nat) : List Step → Bool
  | [] => true
  | s :: ss =>
    (PackedBinaryRows.listProduct s.input 0 (if s.choice then b else a) == s.output) &&
      productsCheck a b ss

lemma productsCheck_append (a b : List Nat) (ss ts : List Step) :
    productsCheck a b (ss ++ ts) = (productsCheck a b ss && productsCheck a b ts) := by
  induction ss with
  | nil => simp [productsCheck]
  | cons s ss ih => simp only [List.cons_append, productsCheck, ih, Bool.and_assoc]

lemma productsCheck_sound (a b : List Nat) (ss : List Step)
    (h : productsCheck a b ss = true) (s : Step) (hs : s ∈ ss) :
    PackedBinaryRows.listProduct s.input 0 (if s.choice then b else a) = s.output := by
  induction ss with
  | nil => simp at hs
  | cons t ts ih =>
    simp only [productsCheck, Bool.and_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · exact ih h.2 hs

/-- Check just the parent indices, choices and output rows, without matrix arithmetic. -/
def layoutCheck : List Nat → List Nat → List Bool → List Step → Bool
  | [], [], [], [] => true
  | y :: ys, p :: ps, c :: cs, s :: ss =>
    (s.output == y) && (s.parent == p) && (s.choice == c) && layoutCheck ys ps cs ss
  | _, _, _, _ => false

lemma layoutCheck_sound (ys ps : List Nat) (cs : List Bool) (ss : List Step)
    (h : layoutCheck ys ps cs ss = true) (i : Nat) (hi : i < ss.length) :
    ss[i]!.output = ys[i]! ∧ ss[i]!.parent = ps[i]! ∧ ss[i]!.choice = cs[i]! := by
  induction ss generalizing ys ps cs i with
  | nil => simp at hi
  | cons s ss ih =>
    cases ys with
    | nil => simp [layoutCheck] at h
    | cons y ys =>
      cases ps with
      | nil => simp [layoutCheck] at h
      | cons p ps =>
        cases cs with
        | nil => simp [layoutCheck] at h
        | cons c cs =>
          simp only [layoutCheck, Bool.and_eq_true, beq_iff_eq] at h
          cases i with
          | zero => simpa only [List.getElem!_cons_zero] using ⟨h.1.1.1, h.1.1.2, h.1.2⟩
          | succ i =>
            simpa only [List.getElem!_cons_succ] using
              ih ys ps cs h.2 i (Nat.lt_of_succ_lt_succ hi)

lemma getElem!_drop {α : Type*} [Inhabited α] (rs : List α) (n i : Nat) :
    (rs.drop n)[i]! = rs[n+i]! := by
  simp only [getElem!_def, List.getElem?_drop]

/-- Consume increasing parent references without restarting a search through the orbit. -/
def inputsCheck (start : Nat) (rs : List Nat) : List Step → Bool
  | [] => true
  | s :: ss =>
    decide (start ≤ s.parent) && (rs.drop (s.parent-start))[0]! == s.input &&
      inputsCheck s.parent (rs.drop (s.parent-start)) ss

lemma inputsCheck_sound (start : Nat) (rs : List Nat) (ss : List Step)
    (h : inputsCheck start rs ss = true) (s : Step) (hs : s ∈ ss) :
    start ≤ s.parent ∧ rs[s.parent-start]! = s.input := by
  induction ss generalizing start rs with
  | nil => simp at hs
  | cons t ts ih =>
    simp only [inputsCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨h.1.1, by simpa only [getElem!_drop, Nat.add_zero] using h.1.2⟩
    · obtain ⟨hle, heq⟩ := ih t.parent (rs.drop (t.parent-start)) h.2 hs
      refine ⟨Nat.le_trans h.1.1 hle, ?_⟩
      rw [getElem!_drop] at heq
      have hadd : t.parent - start + (s.parent - t.parent) = s.parent-start := by omega
      rwa [hadd] at heq

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences
