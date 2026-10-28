module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.Data

/-!
# Exhaustive checking for the first Held involution class

Each row is an actual conjugate of `a`. Checked generator edges, detected
on the certified four-point base, imply coverage of every conjugate.
A Boolean batch checker covers all 24990 indices, including the final partial
batch by reduction modulo 24990. No distinctness or class-size premise is
needed. The row tests discharge exactly the fixed-point contract for 1 and 3.

Source: the seven relations and `M1` in `Held/Model/Source/HeG1-P1.M`.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA

@[expose] public def index (n : Nat) : Fin 24990 :=
  ⟨n % 24990, Nat.mod_lt _ (by decide)⟩

@[expose] public def family (i : Fin 24990) : He := value (data i.val).1

@[expose] public def facts (i : Fin 24990) : Prop :=
  let d := data i.val
  edgeTest d.1 (data (index d.2.1).val).1 (data (index d.2.2.1).val).1 ∧
  rowTest d.1 1 d.2.2.2.1 d.2.2.2.2.1 ∧
  rowTest d.1 3 d.2.2.2.2.2.1 d.2.2.2.2.2.2

public instance (i : Fin 24990) : Decidable (facts i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

@[expose] public def checkNat (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n+1 => checkNat f n && f n

@[expose] public def checkBlock (b : Nat) : Bool :=
  checkNat (fun j => decide (facts (index (64*b+j)))) 64

private theorem checkNat_sound (f : Nat → Bool) (n : Nat)
    (h : checkNat f n = true) (j : Nat) (hj : j < n) : f j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [checkNat, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih h.1 hj
    · exact h.2

public theorem facts_of_blocks
    (h : ∀ b : Fin 400, checkBlock b.val = true) : ∀ i, facts i := by
  intro i
  have hb : i.val / 64 < 400 := by omega
  have ht := checkNat_sound _ 64 (h ⟨i.val / 64, hb⟩) (i.val % 64)
    (Nat.mod_lt _ (by decide))
  have hi : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [index, hi, Nat.mod_eq_of_lt i.isLt, Fin.eta] using of_decide_eq_true ht

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA
