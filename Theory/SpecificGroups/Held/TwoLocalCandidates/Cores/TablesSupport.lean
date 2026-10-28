module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Generators

/-!
# Exhaustive checks on the Held letters

Boolean traversal checks every letter without nested finite quantifiers.
The soundness argument is `List.all_eq_true`, as in the existing J₃
permutation certificates. Only the Lean kernel validates a concrete check.
-/

namespace Held.TwoLocalCandidates.Cores

@[expose] public def checkLetters (f : Fin 2058 → Bool) : Bool :=
  (List.range 2058).all (fun i => f ⟨i % 2058, Nat.mod_lt _ (by decide)⟩)

public theorem allLetters (P : Fin 2058 → Prop) [DecidablePred P]
    (h : checkLetters (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [Nat.mod_eq_of_lt i.isLt, decide_eq_true_eq] using hi

end Held.TwoLocalCandidates.Cores
