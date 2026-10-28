module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.Coordinates
/-! A linear Boolean traversal for kernel-checked finite certificates. -/
@[expose] public section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
def checkFin {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i,h⟩ else true)

theorem allFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
