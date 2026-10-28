module

public import Mathlib.Data.Nat.Bits
public import Lean.Elab.Tactic.Omega

/-!
# Bit-swap networks for the third Fi23 Schreier certificate

A stage exchanges disjoint pairs of bits at a fixed distance. The disjointness
condition is itself a natural-number identity. `run_testBit` proves that a
network acts by its explicit index map on every input bit vector; hence checking
that index map against a published point permutation certifies the action on
all bit vectors. This is the soundness boundary for the compressed permutation
word checks in `Schreier.Checker`.

Application: ATLAS F23G1-p31671B0, the third prefix step used for GLS3 Table 5.3u.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.Schreier.BitNetwork

def swap (d m x : Nat) : Nat :=
  let t := ((x >>> d) ^^^ x) &&& m
  x ^^^ t ^^^ (t <<< d)

def index (d m i : Nat) : Nat :=
  if m.testBit i then d+i else
    if d ≤ i ∧ m.testBit (i-d) = true then i-d else i

theorem swap_testBit (d m : Nat) (h : m &&& (m <<< d) = 0) (x i : Nat) :
    (swap d m x).testBit i = x.testBit (index d m i) := by
  have hm := congrArg (fun n => n.testBit i) h
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at hm
  by_cases hd : d ≤ i
  · have he : d + (i-d) = i := by omega
    simp only [hd, decide_true, Bool.true_and] at hm
    cases hmi : m.testBit i <;> cases hmj : m.testBit (i-d) <;>
      simp_all [swap, index, Nat.testBit_xor, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    all_goals cases x.testBit i <;> cases x.testBit (d+i) <;> rfl
  · cases hmi : m.testBit i <;>
      simp [swap, index, Nat.testBit_xor, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hd, hmi]
    all_goals cases x.testBit i <;> cases x.testBit (d+i) <;> rfl

abbrev Stage := Nat × Nat

def run : List Stage → Nat → Nat
  | [], x => x
  | (d,m)::ss, x => run ss (swap d m x)

def route : List Stage → Nat → Nat
  | [], i => i
  | (d,m)::ss, i => index d m (route ss i)

def Valid (ss : List Stage) : Prop := ∀ s ∈ ss, s.2 &&& (s.2 <<< s.1) = 0

theorem run_testBit (ss : List Stage) (hs : Valid ss) (x i : Nat) :
    (run ss x).testBit i = x.testBit (route ss i) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    rcases s with ⟨d,m⟩
    rw [run, ih (fun s h => hs s (List.mem_cons_of_mem _ h))]
    exact swap_testBit d m (hs _ (List.mem_cons_self)) x _

/-- A finite arithmetic check establishes every stage's disjointness. -/
theorem valid_of_check (ss : List Stage)
    (h : (ss.all fun s => decide (s.2 &&& (s.2 <<< s.1) = 0)) = true) : Valid ss := by
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp h s hs)

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.Schreier.BitNetwork
