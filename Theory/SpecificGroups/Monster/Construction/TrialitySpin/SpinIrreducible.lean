module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinQuotient
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Irreducibility

/-!
# Irreducibility of the concrete first spin action

The actual extraspecial image of `Q1` has order `2^25`, acts faithfully on
the constructed 4096-dimensional spin space, and its central involution
acts as minus identity. The real trace-duality theorem therefore proves
irreducibility. Pullback gives irreducibility for `Q1`; restriction of any
`N1`-invariant subspace then proves irreducibility for `N1` as well.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6 and its Section 27
application, printed pp. 62–63 and 147. All quotient and comparison
premises of the independent irreducibility theorem are discharged here.
-/

public section
namespace Sporadic.Monster.Construction.TrialitySpin.SpinAction

private theorem centerGenerator_mem : q1ImageCenterGenerator ∈ Subgroup.center Q1Image := by
  rw [Q1Image_center]
  exact Subgroup.mem_zpowers _

theorem imageRepresentation_irreducible : Representation.IsIrreducible imageRepresentation := by
  let : IsExtraspecial 2 Q1Image := Q1Image_extraspecial
  exact spinSpace_irreducible_of_extraspecial imageRepresentation Q1Image_card
    centerGenerator_mem q1ImageCenterGenerator_ne_one imageRepresentation_center

theorem q1Representation_irreducible : Representation.IsIrreducible q1Representation := by
  let : IsExtraspecial 2 Q1Image := Q1Image_extraspecial
  exact spinSpace_irreducible_of_quotient q1Representation q1ImageMap
    q1ImageMap_surjective imageRepresentation imageRepresentation_map Q1Image_card
    centerGenerator_mem q1ImageCenterGenerator_ne_one imageRepresentation_center

theorem representation_irreducible : Representation.IsIrreducible representation := by
  let : Representation.IsIrreducible q1Representation := q1Representation_irreducible
  have : Nontrivial (Submodule ℝ SpinSpace) :=
    Function.Injective.nontrivial
      (Subrepresentation.toSubmodule_injective (ρ := q1Representation))
  have : Nontrivial (Subrepresentation representation) := by
    refine ⟨⟨⊥,⊤,?_⟩⟩
    intro h
    exact (bot_ne_top : (⊥ : Submodule ℝ SpinSpace) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)
  constructor
  intro W
  let W' : Subrepresentation q1Representation :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := fun q _ hv => W.apply_mem_toSubmodule (q1Inclusion q) hv }
  rcases eq_bot_or_eq_top W' with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation q1Representation => U.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation q1Representation => U.toSubmodule) h

end Sporadic.Monster.Construction.TrialitySpin.SpinAction
