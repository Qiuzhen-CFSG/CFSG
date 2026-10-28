module

public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.GroupTheory.WordSubgroup
import Mathlib.Tactic.FinCases

/-!
# Finite checking for Rudvalis order witnesses

The witnesses derive from the ATLAS degree-4060 generators stored in
`RuG1-p4060B0.g1` and `RuG1-p4060B0.g2` beside `Model.Basic`.
The inverse point convention preserves the order of word multiplication.
GAP is an untrusted witness generator; all asserted equalities are checked
by Lean's kernel. See `OrderCertificate/GenerateChain.g`.

-/

namespace Rudvalis.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000
set_option Elab.async false

@[expose] public def checkNat (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => checkNat f n && f n

private theorem checkNat_spec (f : Nat → Bool) (n : Nat) :
    checkNat f n = true ↔ ∀ i, i < n → f i = true := by
  induction n with
  | zero => simp [checkNat]
  | succ n ih =>
    rw [checkNat, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, h'⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact h i hlt
      · exact h'
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

@[expose] public def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  checkNat (fun k => if h : k < n then f ⟨k, h⟩ else true) n

public theorem checkFin_spec {n : Nat} (f : Fin n → Bool) :
    checkFin f = true ↔ ∀ i, f i = true := by
  rw [checkFin, checkNat_spec]
  constructor
  · intro h ⟨i, hi⟩
    simpa only [dif_pos hi] using h i hi
  · intro h i hi
    simpa only [dif_pos hi] using h ⟨i, hi⟩

public theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  exact of_decide_eq_true ((checkFin_spec _).mp h i)

public theorem allFin₂ {n m : Nat} (P : Fin n → Fin m → Prop)
    [∀ i j, Decidable (P i j)]
    (h : checkFin (fun i => checkFin (fun j => decide (P i j))) = true) :
    ∀ i j, P i j := by
  intro i
  exact allFin _ ((checkFin_spec _).mp h i)

public theorem allFin₃ {n m p : Nat} (P : Fin n → Fin m → Fin p → Prop)
    [∀ i j k, Decidable (P i j k)]
    (h : checkFin (fun i => checkFin (fun j => checkFin (fun k => decide (P i j k)))) = true) :
    ∀ i j k, P i j k := by
  intro i
  exact allFin₂ _ ((checkFin_spec _).mp h i)

/-- Decode a word of the specified length from its base-`n + 1` digits. -/
@[expose] public def unpackWord (n : Nat) : Nat → Nat → List (Fin (n + 1))
  | _, 0 => []
  | code, len + 1 =>
    ⟨code % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩ ::
      unpackWord n (code / (n + 1)) len


end Rudvalis.OrderCertificate
