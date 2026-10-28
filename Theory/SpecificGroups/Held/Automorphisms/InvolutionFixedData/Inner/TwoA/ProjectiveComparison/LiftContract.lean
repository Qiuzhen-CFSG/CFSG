module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.Model
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.Coordinates

/-!
# The concrete Held generator-action certificate

The remaining finite obligation consists of two elements of the literal
commutator subgroup of the 2A centralizer, acting on the 21 explicitly labelled
ambient points by `permA` and `permB`. This is a finite action certificate,
not an assumed quotient isomorphism or subgroup recognition theorem.
The second theorem translates those equations into the actual projective
matrix action already certified in `Coordinates`.

Source: GLS3 Table 5.3p; the retained Held generator words and their inverse
permutations are in the parent cover task's `Scratch/HeldTwoACover/discovery.json`.
-/

@[expose] public section
namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison

/-- The concrete certificate left to the Held word calculation. -/
def GeneratorLifts : Prop := ∃ x y : derived,
  (∀ i : Fin 21, representation x.val.val (pointLabel i) = pointLabel (permA i)) ∧
  (∀ i : Fin 21, representation y.val.val (pointLabel i) = pointLabel (permB i))

theorem label_generator_lifts (hl : GeneratorLifts) :
    ∀ s ∈ ({projectiveA, projectiveB} : Set PSL),
      ∃ d : derived, ∀ p : PG, d • label p = label (s • p) := by
  obtain ⟨x, y, hx, hy⟩ := hl
  intro s hs
  rcases hs with rfl | hs
  · refine ⟨x, ?_⟩
    intro p
    obtain ⟨i, rfl⟩ := pointEquiv.surjective p
    rw [projectiveA_point, label_pointEquiv, label_pointEquiv]
    exact hx i
  · rw [Set.mem_singleton_iff] at hs
    subst s
    refine ⟨y, ?_⟩
    intro p
    obtain ⟨i, rfl⟩ := pointEquiv.surjective p
    rw [projectiveB_point, label_pointEquiv, label_pointEquiv]
    exact hy i

end Held.InvolutionFixedData.TwoA.ProjectiveComparison
