module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraph

/-!
# Cycle bounds for separated class graphs

A cycle shorter than the separation radius splits into two unequal short
paths with the same endpoints, contradicting unique lifting to the tree.
This supplements the class-cover API without changing its ball-fixer API.

Source application: DGS, Groups and Graphs (1985), (3.6), pp.77--78.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} {Γ : SimpleGraph V} {r : Setoid V} {m : ℕ}

/-- Separation bounds every cycle of the raw class graph. -/
theorem classGraph_cycle_length (ht : Γ.IsTree) (hsep : Separated r Γ m)
    (hlift : NeighborLifting Γ r) {a : Quotient r}
    (p : (classGraph Γ r).Walk a a) (hp : p.IsCycle) : m ≤ p.length := by
  by_contra hn
  have hthree := hp.three_le_length
  have he := classGraph_short_paths_unique ht hsep hlift
    (p.take 1) (p.drop 1).reverse (hp.isPath_take (by omega))
    (hp.isPath_drop (by omega)).reverse (by
      simp only [take_length, length_reverse, drop_length]
      omega)
  have hh := congrArg (fun w => w.length) he
  simp only [take_length, length_reverse, drop_length] at hh
  omega

end Theory.GroupTheory.WeakBNPair.RegularTree
