module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants

/-!
# Fixed spaces of normal subgroups

The fixed vectors of a normal subgroup form a subrepresentation of the whole
group: conjugating a subgroup element transports the fixed-vector condition.
For an irreducible representation, a nonzero such fixed space must therefore
be the entire space, so the normal subgroup lies in the representation kernel.
Neither finiteness of the group nor finite dimension is required.

These are the normal-invariants lemmas from the historical
`Submission/FeitThompson/Representation/SolvableDimension.lean` at commit
`c3503435`, extracted as a reusable prerequisite of the modular kernel argument.
The fixed-subrepresentation definition is exposed because its underlying
submodule is intentionally the existing `Representation.invariants`.
-/

namespace Representation

/-- The fixed space of a normal subgroup is an ambient subrepresentation. -/
@[expose] public noncomputable def fixedSubrepresentationOfNormal
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (H : Subgroup G) [H.Normal] : Subrepresentation ρ where
  toSubmodule := Representation.invariants (ρ.comp H.subtype)
  apply_mem_toSubmodule := Representation.le_comap_invariants ρ H

/-- A normal subgroup with a nonzero fixed vector acts trivially on an
irreducible representation. -/
public theorem le_ker_of_normal_invariants_ne_bot
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (H : Subgroup G) [H.Normal] [Representation.IsIrreducible ρ]
    (hfix : Representation.invariants (ρ.comp H.subtype) ≠ ⊥) : H ≤ ρ.ker := by
  let S := fixedSubrepresentationOfNormal ρ H
  have hS_ne : S ≠ ⊥ := fun hS => hfix (congrArg Subrepresentation.toSubmodule hS)
  have hS_top : S = ⊤ :=
    ((inferInstance : Representation.IsIrreducible ρ).eq_bot_or_eq_top S).resolve_left hS_ne
  have htop : Representation.invariants (ρ.comp H.subtype) = ⊤ :=
    congrArg Subrepresentation.toSubmodule hS_top
  intro h hh
  rw [MonoidHom.mem_ker]
  ext v
  have hv : v ∈ Representation.invariants (ρ.comp H.subtype) := by simp [htop]
  exact hv ⟨h, hh⟩

end Representation
