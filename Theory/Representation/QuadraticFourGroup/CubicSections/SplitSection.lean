module

public import Theory.Representation.QuadraticFourGroup.CubicSections.Descent

/-!
# Split actions containing a prescribed section

`SplitOrbit` records an actual embedding of the product of two concrete
PSL₂ groups into an acting group, the source quadratic four-group hypotheses
for its first factor, and equality with the actual component orbit.
`SplitSectionWitness` further records a faithful irreducible ambient action
in which a specified product representation occurs as an invariant
subquotient. Faithfulness is part of the source `Hypotheses`.

These are output interfaces for the faithful-image and Clifford reductions
in GLS, volume 2, Theorem 25.14, Step 2. They assert no existence theorem.
`HasCubicInverters` is the precise local group fact required in Step 4;
it contains no representation-theoretic conclusion.
-/

@[expose] public section

universe u v w

namespace Representation.QuadraticFourGroup

/-- The local group fact consumed by the cubic dihedral construction. -/
def HasCubicInverters (H : Type*) [Group H] : Prop :=
  ∀ x : H, orderOf x = 3 → ∃ b : H, b * b = 1 ∧ b * x * b⁻¹ = x⁻¹

/-- A split component orbit inside the actual acting group. -/
structure SplitOrbit {Q U : Type*} [Group Q]
    [AddCommGroup U] [Module (ZMod 2) U]
    (τ : Representation (ZMod 2) Q U) (n : ℕ) where
  one_lt : 1 < n
  embedding : Factor n × Factor n →* Q
  injective : Function.Injective embedding
  fourGroup : Subgroup Q
  involution : Q
  hypotheses : Hypotheses τ
    (embedding.comp (MonoidHom.inl (Factor n) (Factor n))).range fourGroup involution
  orbit_eq : Theory.GroupTheory.componentOrbit
    (embedding.comp (MonoidHom.inl (Factor n) (Factor n))).range fourGroup = embedding.range

set_option linter.checkUnivs false in
/-- A faithful irreducible ambient action with split orbit containing a given
section on restriction. All representations are actual linear actions. -/
structure SplitSectionWitness {n : ℕ} {W : Type w}
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (Factor n × Factor n) W) where
  Actor : Type u
  [actorGroup : Group Actor]
  [actorFinite : Finite Actor]
  Space : Type v
  [spaceAdd : AddCommGroup Space]
  [spaceModule : Module (ZMod 2) Space]
  [spaceFiniteDimensional : FiniteDimensional (ZMod 2) Space]
  action : Representation (ZMod 2) Actor Space
  irreducible : action.IsIrreducible
  split : SplitOrbit action n
  isSection : IsIrreducibleSection (action.comp split.embedding) σ

attribute [instance] SplitSectionWitness.actorGroup SplitSectionWitness.actorFinite
  SplitSectionWitness.spaceAdd SplitSectionWitness.spaceModule
  SplitSectionWitness.spaceFiniteDimensional

end Representation.QuadraticFourGroup

end
