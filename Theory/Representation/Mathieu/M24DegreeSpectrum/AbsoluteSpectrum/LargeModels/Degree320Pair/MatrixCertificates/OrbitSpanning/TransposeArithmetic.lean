module

public import Mathlib.Data.Nat.Bits
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.Arithmetic


/-!
# Packed transpose certificates

Each column is packed by reading the source row list in order. The bit theorem
identifies the packed integer with the corresponding transposed column. Small
checks of consecutive columns are assembled by a proved append identity.
This certifies the literal generator and basis transposes used by the left
orbit proof. Source attribution and measurements: `source/README.md`.
-/

@[expose] public section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates
open Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels

def packedColumn (d : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.bit (decide (x / d % 2 = 1)) (packedColumn d xs)

theorem packedColumn_bit (i : Nat) (a : List Nat) (j : Nat) (hj : j < a.length) :
    (packedColumn (2^i) a).testBit j = a[j]!.testBit i := by
  induction a generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      rw [packedColumn, Nat.testBit_bit_zero, List.getElem!_cons_zero]
      exact Nat.testBit_eq_decide_div_mod_eq.symm
    | succ j =>
      simpa only [packedColumn, Nat.testBit_bit_succ, List.getElem!_cons_succ] using
        ih j (Nat.lt_of_succ_lt_succ hj)

def checkColumn (d c : Nat) (a : List Nat) : Bool := packedColumn d a == c

theorem checkColumn_sound (i c : Nat) (a : List Nat) (h : checkColumn (2^i) c a = true)
    (j : Nat) (hj : j < a.length) : a[j]!.testBit i = c.testBit j := by
  have hh : packedColumn (2^i) a = c := of_decide_eq_true h
  rw [← hh, packedColumn_bit i a j hj]

def transposeRows (a : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, c :: cs => checkColumn (2^i) c a && transposeRows a (i+1) cs

theorem transposeRows_get (a b : List Nat) (s : Nat) (h : transposeRows a s b = true)
    (i : Nat) (hi : i < b.length) : checkColumn (2^(s+i)) b[i]! a = true := by
  induction b generalizing s i with
  | nil => simp at hi
  | cons c cs ih =>
    simp only [transposeRows, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (s+1) h.2 i (Nat.lt_of_succ_lt_succ hi)

theorem transposeRows_append (a b c : List Nat) (i : Nat)
    (hb : transposeRows a i b = true)
    (hc : transposeRows a (i+b.length) c = true) : transposeRows a i (b++c) = true := by
  induction b generalizing i with
  | nil => simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hc
  | cons x xs ih =>
    simp only [transposeRows, Bool.and_eq_true] at hb
    simp only [List.cons_append, transposeRows, Bool.and_eq_true]
    refine ⟨hb.1, ih (i+1) hb.2 ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

theorem transpose_check (n : Nat) (a b : List Nat) (ha : a.length = n) (hb : b.length = n)
    (h : transposeRows a 0 b = true) :
    OneSixty.checkTranspose n a.toArray b.toArray = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hc := transposeRows_get a b 0 h i (by simpa [hb] using List.mem_range.mp hi)
  apply List.all_eq_true.mpr
  intro j hj
  have he := checkColumn_sound i b[i]! a (by simpa only [Nat.zero_add] using hc)
    j (by simpa [ha] using List.mem_range.mp hj)
  simpa only [List.getElem!_toArray, beq_iff_eq] using he

theorem transposeRows_append_at (a b c : List Nat) (i j : Nat)
    (hij : i+b.length = j) (hb : transposeRows a i b = true)
    (hc : transposeRows a j c = true) : transposeRows a i (b++c) = true := by
  apply transposeRows_append a b c i hb
  rw [hij]
  exact hc

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates
