module

public import Mathlib.Data.Nat.Bits
public import Lean.Elab.Tactic.Omega

/-!
# Checked transformations of graph row bit masks

Each stage selects bits from three shifted copies of its input. The partial
coordinate route checks which copy supplies a bit, and its soundness theorem
identifies that bit without any assumption about the supplied masks. Composing
stages gives a compact certificate for a permutation of graph columns.

Used for the exact ATLAS F22G1-p3510B0 graph certificate (GLS3 Table 5.3t).
-/

@[expose] public section

namespace Sporadic.Fischer.Fi22.KernelCertificate.BitNetwork
structure Stage where
  distance : Nat
  low : Nat
  high : Nat
  stay : Nat

def Stage.apply (s : Stage) (v : Nat) : Nat :=
  ((v >>> s.distance) &&& s.low) |||
  ((v <<< s.distance) &&& s.high) ||| (v &&& s.stay)

def Stage.route (s : Stage) (i : Nat) : Option Nat :=
  match s.low.testBit i, s.high.testBit i, s.stay.testBit i with
  | true, false, false => some (s.distance + i)
  | false, true, false => if s.distance ≤ i then some (i - s.distance) else none
  | false, false, true => some i
  | _, _, _ => none

theorem Stage.sound (s : Stage) (i j v : Nat) (h : s.route i = some j) :
    (s.apply v).testBit i = v.testBit j := by
  simp only [Stage.route] at h
  cases hl : s.low.testBit i <;> cases hh : s.high.testBit i <;>
    cases hk : s.stay.testBit i <;>
    simp only [hl, hh, hk] at h <;> try { cases h }
  · simpa only [Stage.apply, Nat.testBit_or, Nat.testBit_and,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hl, hh, hk,
      Bool.and_false, Bool.and_true, Bool.false_or, Bool.or_false] using congrArg (v.testBit) (Option.some.inj h)
  · split at h
    next hi =>
      cases Option.some.inj h
      simp [Stage.apply, hl, hh, hk, hi]
    next => cases h
  · cases Option.some.inj h
    simp [Stage.apply, hl, hh, hk]

def apply : List Stage → Nat → Nat
  | [], v => v
  | s :: ss, v => s.apply (apply ss v)

def route : List Stage → Nat → Option Nat
  | [], i => some i
  | s :: ss, i => (s.route i).bind (route ss)

theorem sound (ss : List Stage) (i j v : Nat) (h : route ss i = some j) :
    (apply ss v).testBit i = v.testBit j := by
  induction ss generalizing i with
  | nil => cases Option.some.inj h; rfl
  | cons s ss ih =>
    simp only [route] at h
    cases hs : s.route i with
    | none => simp [hs] at h
    | some k =>
      rw [apply, s.sound i k _ hs]
      exact ih k (by simpa only [hs, Option.bind_some] using h)

-- Enumerate natural indices without constructing a Finset or proof-carrying list.
def check (p : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | start, count + 1 => p start && check p (start + 1) count

theorem check_sound (p : Nat → Bool) (start count : Nat)
    (h : check p start count = true) (i : Nat) (hlo : start ≤ i) (hhi : i < start + count) :
    p i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hi : i = start
    · simpa [hi] using h.1
    · exact ih (start + 1) h.2 (by omega) (by omega)
theorem check_append (p : Nat → Bool) (start a b : Nat)
    (ha : check p start a = true) (hb : check p (start + a) b = true) :
    check p start (a + b) = true := by
  induction a generalizing start with
  | zero => simpa using hb
  | succ a ih =>
    simp only [check, Bool.and_eq_true] at ha
    rw [Nat.succ_add, check, Bool.and_eq_true]
    exact ⟨ha.1, ih (start + 1) ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩
end Sporadic.Fischer.Fi22.KernelCertificate.BitNetwork
