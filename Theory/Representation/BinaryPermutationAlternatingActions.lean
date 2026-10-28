module

public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Common alternating permutation actions

The alternating full, augmentation and natural actions, and the projection from
augmentation to the natural section, are shared by the submodule-structure and
cohomology developments. Keeping one definition of each allows their results to
be imported together.

Source: Aschbacher–Smith, §B.3, printed p.83, and I.1.6(1), printed p.408.
-/

@[expose] public section

namespace BinaryPermutation
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω]

/-- The full permutation module restricted to the alternating group. -/
abbrev alternatingRepresentation : Representation (ZMod 2) (alternatingGroup Ω) (Full Ω) :=
  (representation Ω).comp (alternatingGroup Ω).subtype

/-- The augmentation kernel restricted to the alternating group. -/
abbrev alternatingCoreRepresentation : Representation (ZMod 2) (alternatingGroup Ω) (core Ω) :=
  (coreRepresentation Ω).comp (alternatingGroup Ω).subtype

/-- The natural deleted-permutation section restricted to the alternating group. -/
abbrev alternatingNaturalRepresentation : Representation (ZMod 2) (alternatingGroup Ω) (natural Ω) :=
  (naturalRepresentation Ω).comp (alternatingGroup Ω).subtype

/-- The quotient map from the augmentation kernel onto the natural section. -/
def coreToNatural : core Ω →ₗ[ZMod 2] natural Ω :=
  ((constants Ω).mkQ.domRestrict (core Ω)).codRestrict (natural Ω)
    (fun v => ⟨v.val, v.property, rfl⟩)

end BinaryPermutation
