module

public import Mathlib.Init

/-!
# Linear predecessor checking

A single pass through a predecessor list certifies that every positive index
points backwards. The soundness proof avoids repeating literal array lookup
in a finite universal check. This is used on both degree-1408 orbit tables.
-/

@[expose] public section

namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity

def parentsBefore (start : Nat) : List Nat → Bool
  | [] => true
  | p :: ps => (decide (start = 0) || decide (p < start)) && parentsBefore (start + 1) ps

lemma parentsBefore_sound (start : Nat) (ps : List Nat)
    (h : parentsBefore start ps = true) :
    ∀ i (hi : i < ps.length), 0 < start + i → ps[i] < start + i := by
  induction ps generalizing start with
  | nil => simp
  | cons p ps ih =>
    simp only [parentsBefore, Bool.and_eq_true] at h
    intro i hi hpos
    cases i with
    | zero =>
      simp only [Nat.add_zero] at hpos ⊢
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h.1 with hs | hp
      · omega
      · exact hp
    | succ i =>
      have hi' : i < ps.length := Nat.lt_of_succ_lt_succ hi
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using
        ih (start + 1) h.2 i hi' (by omega)
end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
