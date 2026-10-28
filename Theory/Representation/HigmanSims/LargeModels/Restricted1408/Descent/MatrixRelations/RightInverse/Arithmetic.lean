module

public import Theory.LinearAlgebra.PackedBinaryRows

/-!
# Soundness of the blockwise packed right-inverse certificate

Concatenating row blocks is XOR of their row actions, with the position offset
advanced by the length of each block. A successful `checkRows` computes every
listed row to its designated coordinate vector. These facts connect the small
literal checks to the original packed-row API without any computational oracle.

Application and source: the ATLAS degree-1408 restriction, in `RightInverse`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.RightInverse
open PackedBinaryRows

def blockProduct (x start : Nat) : List (List Nat) → Nat
  | [] => 0
  | rs :: rss => listProduct x start rs ^^^ blockProduct x (start + rs.length) rss

def checkRows (rhs : List (List Nat)) (start : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => (blockProduct x 0 rhs == 2 ^ start) && checkRows rhs (start + 1) xs

theorem listProduct_append (x start : Nat) (as bs : List Nat) :
    listProduct x start (as ++ bs) =
      listProduct x start as ^^^ listProduct x (start + as.length) bs := by
  induction as generalizing start with
  | nil => simp [listProduct]
  | cons a as ih =>
    simp only [List.cons_append, listProduct, List.length_cons, ih, Nat.xor_assoc]
    rw [show start + 1 + as.length = start + (as.length + 1) by omega]

theorem blockProduct_sound (x start : Nat) (rs : List (List Nat)) :
    blockProduct x start rs = listProduct x start rs.flatten := by
  induction rs generalizing start with
  | nil => rfl
  | cons rs rss ih =>
    rw [blockProduct, List.flatten_cons, listProduct_append, ih]

theorem checkRows_sound (rhs : List (List Nat)) (rs : List Nat) (start : Nat)
    (h : checkRows rhs start rs = true) (i : Nat) (hi : i < rs.length) :
    blockProduct rs[i]! 0 rhs = 2 ^ (start + i) := by
  induction rs generalizing start i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [checkRows, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hh := ih (start + 1) h.2 i (by simpa using hi)
      simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using hh
end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.RightInverse
