module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.Inputs
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.Coordinates
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity

/-!
# Assembly of the two geometric PSL₃(3) models

The point augmentation module and the incidence cycle quotient are genuine
representations of the canonical projective matrix group, with proved
dimensions twelve and twenty-six. Their coordinate equivalences transport
simplicity to precisely the carriers requested by `PrincipalModelsExist`.

The checked actor matrices generate the full endomorphism algebra of each
geometric model over every characteristic-two field. Transporting their
irreducibility proves the existence contract in arbitrary universes, without
any additional construction or simplicity premise.

Source application: Guralnick--Malle, *Classification of 2F-modules I*,
Proposition 4.2, manuscript pp.9--10, and the principal-block degrees in the
characteristic-two L₃(3) decomposition matrix.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels
variable (F : Type*) [Field F] [CharP F 2]

omit [CharP F 2] in
private lemma irreducible_transport {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F Group V} {σ : Representation F Group W}
    (e : ρ.Equiv σ) (h : IsIrreducible ρ) : IsIrreducible σ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mp ((irreducible_iff_isSimpleModule_asModule ρ).mp h)

omit [CharP F 2] in
lemma degree12_irreducible_of_pointCore
    (h : IsIrreducible (pointCore F).toRepresentation) : IsIrreducible (degree12 F) :=
  irreducible_transport F (pointCoreEquiv F) h

lemma degree26_irreducible_of_cycleQuotient
    (h : IsIrreducible (constantLine F).quotientRepresentation) : IsIrreducible (degree26 F) :=
  irreducible_transport F (cycleQuotientEquiv F) h

/-- The twelve-coordinate point augmentation model is simple over every
characteristic-two field. -/
theorem degree12_isIrreducible : IsIrreducible (degree12 F) :=
  degree12_irreducible_of_pointCore F (pointCore_isIrreducible F)

/-- The twenty-six-coordinate incidence-cycle quotient is simple over every
characteristic-two field. -/
theorem degree26_isIrreducible : IsIrreducible (degree26 F) :=
  degree26_irreducible_of_cycleQuotient F (cycleQuotient_isIrreducible F)

end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels

namespace Representation.PSL3Three.AbsoluteDegrees
universe v
open PrincipalModels

/-- The exact construction contract follows once both geometric simplicity
proofs are supplied. Neither premise is asserted by this conditional assembly. -/
theorem principalModelsExist_of_geometric_irreducibility
    (h₁₂ : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
      IsIrreducible (pointCore F).toRepresentation)
    (h₂₆ : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
      IsIrreducible (constantLine F).quotientRepresentation) : PrincipalModelsExist.{v} := by
  intro F _ _ _
  exact ⟨degree12 F, degree26 F, degree12_irreducible_of_pointCore F (h₁₂ F),
    degree26_irreducible_of_cycleQuotient F (h₂₆ F)⟩

/-- Actual simple representations of the native PSL₃(3) on twelve and
twenty-six coordinates over every algebraically closed characteristic-two
field. Both geometric simplicity premises are discharged. -/
theorem principalModelsExist : PrincipalModelsExist.{v} := by
  intro F _ _ _
  exact ⟨degree12 F, degree26 F, degree12_isIrreducible F, degree26_isIrreducible F⟩

end Representation.PSL3Three.AbsoluteDegrees
