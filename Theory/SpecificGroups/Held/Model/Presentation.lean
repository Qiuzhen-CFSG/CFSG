module

public import Theory.SpecificGroups.Held.Model.Basic
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The presentation map onto the concrete Held model

The seven ATLAS relations define a presented group and a canonical surjection
onto the degree-2058 permutation model. The map is constructed using the
kernel-checked relators; surjectivity follows because its image contains both
standard generators. This does not claim that the presentation map is injective.

Source: John Bray's ATLAS presentation `HeG1-P1`, retained in
`Model/Source/HeG1-P1.M`.
-/

namespace Held

/-- The relators in the free group on two explicitly indexed generators. -/
@[expose] public def definingRelators : Set (FreeGroup (Fin 2)) :=
  Set.range (relationWord (FreeGroup.of 0) (FreeGroup.of 1))

/-- The independent group presented by John Bray's seven ATLAS relators. -/
public abbrev Presentation := PresentedGroup definingRelators

/-- Assignment of the two presentation generators to the concrete permutations. -/
@[expose] public def generator : Fin 2 → He
  | 0 => a
  | 1 => b

private theorem lift_relators (r : FreeGroup (Fin 2)) (hr : r ∈ definingRelators) :
    FreeGroup.lift generator r = 1 := by
  obtain ⟨i, rfl⟩ := hr
  rw [map_relationWord]
  simpa only [FreeGroup.lift_apply_of, generator] using relations i

/-- The canonical homomorphism from the ATLAS presentation to the concrete group. -/
public def presentationMap : Presentation →* He :=
  PresentedGroup.toGroup lift_relators

@[simp] public theorem presentationMap_of (i : Fin 2) :
    presentationMap (PresentedGroup.of i) = generator i :=
  PresentedGroup.toGroup.of lift_relators

/-- The checked concrete model is a quotient of the sourced presentation. -/
public theorem presentationMap_surjective : Function.Surjective presentationMap := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← closure_pair, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨PresentedGroup.of 0, presentationMap_of 0⟩
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨PresentedGroup.of 1, presentationMap_of 1⟩

end Held
