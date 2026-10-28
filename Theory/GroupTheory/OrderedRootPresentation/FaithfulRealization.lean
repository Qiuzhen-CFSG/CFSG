module
public import Theory.GroupTheory.OrderedRootPresentation.Realization

/-!
# Faithfulness of an ordered-root realization

If both sets of ordered coordinates are unique, the homomorphism transported
from the native ordered subgroup is injective. This is a direct consequence
of the two restricted evaluation isomorphisms and needs no cardinal argument.
It supplies faithful transfer for the source prefix and suffix comparisons.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.OrderedRootPresentation
open Subgroup
universe u v
variable {I : Type u} {R : I → Type v} [∀ i, Group (R i)] [DecidableEq I]
  {order : List I} (d : Table R order)
  {G H : Type*} [Group G] [Group H]
  {x : ∀ i, R i →* G} {y : ∀ i, R i →* H}

/-- Unique target words make the transported native realization faithful. -/
theorem realization_injective (E : Equations d x) (F : Equations d y)
    (hn : order.Nodup)
    (hi : Function.Injective (word R (fun i => x i) order))
    (hj : Function.Injective (word R (fun i => y i) order)) :
    Function.Injective (realization d E F hn hi) := by
  intro a b hab
  have he : orderedEval d F hn ((orderedEquiv d E hn hi).symm a) =
      orderedEval d F hn ((orderedEquiv d E hn hi).symm b) := by
    apply Subtype.ext
    exact hab
  exact (orderedEquiv d E hn hi).symm.injective
    ((orderedEval_bijective d F hn hj).1 he)

end Theory.GroupTheory.OrderedRootPresentation
