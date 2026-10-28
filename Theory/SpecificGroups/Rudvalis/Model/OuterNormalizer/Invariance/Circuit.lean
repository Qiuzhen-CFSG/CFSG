module

public import Mathlib.GroupTheory.Perm.Finite

/-!
# Soundness of packed bit-routing circuits

Each stage selects, shifts and joins disjoint sets of bits. The partial
routing interpreter rejects positions with missing or overlapping sources.
A successful route therefore proves the output bit equals the named input
bit, for every input natural number. No circuit data is trusted.

This is the computation bridge used for the degree-4060 ATLAS permutations
in the Rudvalis orbital calculation (GLS3, Table 5.3r, printed p.279).
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate
public structure Stage where
  shift : Nat
  keep : Nat
  low : Nat
  high : Nat

@[expose] public def Stage.eval (s : Stage) (n : Nat) : Nat :=
  (n &&& s.keep) ||| ((n >>> s.shift) &&& s.low) |||
    ((n <<< s.shift) &&& s.high)

@[expose] public def Stage.route (s : Stage) (i : Nat) : Option Nat :=
  match s.keep.testBit i, s.low.testBit i, s.high.testBit i with
  | true, false, false => some i
  | false, true, false => some (s.shift + i)
  | false, false, true => if s.shift ≤ i then some (i - s.shift) else none
  | _, _, _ => none

public theorem Stage.sound (s : Stage) (i j n : Nat) (h : s.route i = some j) :
    (s.eval n).testBit i = n.testBit j := by
  unfold route at h
  simp only [eval, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  cases hk : s.keep.testBit i <;> cases hl : s.low.testBit i <;>
    cases hh : s.high.testBit i <;> simp only [hk, hl, hh] at h ⊢ <;>
    simp only [Bool.and_false, Bool.and_true, Bool.or_false, Bool.false_or] at *
  all_goals try contradiction
  · split at h
    · cases h; simp_all
    · contradiction
  · cases h; rfl
  · cases h; rfl

@[expose] public def eval : List Stage → Nat → Nat
  | [], n => n
  | s :: ss, n => s.eval (eval ss n)

@[expose] public def route : List Stage → Nat → Option Nat
  | [], i => some i
  | s :: ss, i => (s.route i).bind (route ss)

public theorem sound (ss : List Stage) (i j n : Nat) (h : route ss i = some j) :
    (eval ss n).testBit i = n.testBit j := by
  induction ss generalizing i with
  | nil => cases h; rfl
  | cons s ss ih =>
    obtain ⟨k, hk, hj⟩ := Option.bind_eq_some_iff.mp h
    exact (s.sound i k (eval ss n) hk).trans (ih k hj)
end Rudvalis.OuterNormalizer.InvarianceCertificate
