module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.MatrixEquations.Packed

/-!
# Streaming binary row products and bounded certificates

Reading successive rows and dividing the selector by two avoids repeated
indexed lookup of the right-hand matrix. XOR soundness identifies each output
bit with the finite dot product. The theorem `stream_eq_product` explicitly
requires the list to be in the same order as the blocked matrix rows; a
separate literal-data certificate can discharge this equality once per matrix.

`checkBlock_sound` turns a kernel-reduced Boolean check on a bounded interval
into row equalities. `combine_chunks` joins adjacent intervals without
recomputing their certificates. The data provenance and column convention
are documented in `Conjugacy/source/README.md`.
-/

open scoped BigOperators
namespace BabyMonster.OrderLowerBound.ConjugacyCertificate
open Thompson.BinaryMatrix

@[expose] public def stream : List Nat → Nat → Nat
  | [], _ => 0
  | r :: rs, a => if a.testBit 0 then r ^^^ stream rs (a / 2) else stream rs (a / 2)

private theorem bit_div_two (a k : Nat) : bit (a / 2) k = bit a (k + 1) := by
  simp only [bit, Nat.testBit_div_two]

public theorem bit_stream (rs : List Nat) (a j : Nat) :
    bit (stream rs a) j = ∑ k ∈ Finset.range rs.length, bit a k * bit rs[k]! j := by
  induction rs generalizing a with
  | nil => simp [stream, bit]
  | cons r rs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    rw [stream]
    split_ifs with h
    · rw [bit_xor, ih]
      simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, bit_div_two]
      rw [show bit a 0 = 1 by simp [bit, h], one_mul, add_comm]
    · rw [ih]
      simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, bit_div_two]
      rw [show bit a 0 = 0 by simp [bit, h], zero_mul, add_zero]

public theorem bit_stream_ofFn (n : Nat) (f : Fin n → Nat) (a j : Nat) :
    bit (stream (List.ofFn f) a) j = ∑ k : Fin n, bit a k.val * bit (f k) j := by
  have h := bit_stream (List.ofFn f) a j
  rw [List.length_ofFn] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < (List.ofFn f).length := by simp
  simp only [getElem!_pos (c := List.ofFn f) (i := i.val) hi, List.getElem_ofFn]

public theorem stream_eq_product (n : Nat) (b : Array (Array Nat)) (rs : List Nat)
    (hr : rs = List.ofFn (fun i : Fin n => row b i.val)) (a : Nat) :
    stream rs a = product a b n := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h := bit_stream_ofFn n (fun i : Fin n => row b i.val) a j
  rw [← hr, Fin.sum_univ_eq_sum_range (fun k => bit a k * bit (row b k) j), ← bit_product] at h
  unfold bit at h
  cases h₁ : (stream rs a).testBit j <;> cases h₂ : (product a b n).testBit j <;>
    simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals simp only [zero_ne_one, one_ne_zero] at h

@[expose] public def checkBlock (f g : Nat → Nat) (start count : Nat) : Bool :=
  (List.range' start count).all (fun i => f i == g i)

public theorem checkBlock_sound (f g : Nat → Nat) (start count : Nat)
    (h : checkBlock f g start count = true) (i : Fin count) :
    f (start + i.val) = g (start + i.val) := by
  have hm : start + i.val ∈ List.range' start count := by
    exact List.mem_range'.mpr ⟨i.val, i.isLt, by omega⟩
  have hh := List.all_eq_true.mp h (start + i.val) hm
  simpa only [Nat.beq_eq_true_eq] using hh

public theorem combine_chunks (P : Nat → Prop) (start a b : Nat)
    (ha : ∀ i : Fin a, P (start + i.val))
    (hb : ∀ i : Fin b, P (start + a + i.val)) :
    ∀ i : Fin (a + b), P (start + i.val) := by
  intro i
  by_cases hi : i.val < a
  · exact ha ⟨i.val, hi⟩
  · have hj : i.val - a < b := by omega
    have h := hb ⟨i.val - a, hj⟩
    change P (start + a + (i.val - a)) at h
    rwa [show start + a + (i.val - a) = start + i.val by omega] at h

end BabyMonster.OrderLowerBound.ConjugacyCertificate
