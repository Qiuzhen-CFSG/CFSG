module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Words

/-!
# Kernel checking of representative permutation tables

The Boolean traversal covers every letter of the fixed degree-2058 carrier.
It is only an evaluation aid; every concrete certificate is reduced by the
Lean kernel, with no external evaluation axiom.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages

def checkLetters (f : Fin 2058 → Bool) : Bool :=
  (List.range 2058).all (fun i => f ⟨i % 2058, Nat.mod_lt _ (by decide)⟩)

theorem allLetters (P : Fin 2058 → Prop) [DecidablePred P]
    (h : checkLetters (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [Nat.mod_eq_of_lt i.isLt, decide_eq_true_eq] using hi

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
