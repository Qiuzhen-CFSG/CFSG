module

public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# Concrete quotients by solvable kernels

A model records an actual multiplicative equivalence from a quotient by a
solvable normal subgroup. The normal subgroup is relative to the group
being quotiented. The normal-image alternative transports every nonsolvable
simple section to a section of the concrete quotient model.

This is the elementary solvable-layer reduction used in classical parabolic
calculations. It makes no assertion that a given group has such a model.
-/

public noncomputable section

universe u v w

namespace Group

/-- An actual model for a quotient by a solvable normal subgroup. -/
structure SolvableKernelModel (G : Type u) (H : Type v) [Group G] [Group H] where
  kernel : Subgroup G
  normal : kernel.Normal
  solvable : Group.IsSolvable kernel
  quotientEquiv : letI := normal; (G ⧸ kernel) ≃* H

namespace SolvableKernelModel

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Removing the solvable kernel transports each nonsolvable simple section
to a subgroup of the specified concrete quotient model. -/
theorem simple_section (m : SolvableKernelModel G H)
    {S : Type w} [Group S] [IsSimpleGroup S] (hS : ¬ Group.IsSolvable S)
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    ∃ V : Subgroup H, ∃ g : V →* S, Function.Surjective g := by
  let := m.normal
  let := m.solvable
  obtain ⟨V, g, hg⟩ := Subgroup.simple_section_quotient_of_solvable_kernel hS m.kernel U f hf
  let e := Subgroup.equivMapOfInjective V m.quotientEquiv.toMonoidHom m.quotientEquiv.injective
  exact ⟨V.map m.quotientEquiv.toMonoidHom, g.comp e.symm.toMonoidHom,
    hg.comp e.symm.surjective⟩

end SolvableKernelModel

end Group
