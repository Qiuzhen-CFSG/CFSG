module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.ActionTable
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.ComparisonA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.ComparisonB

/-!
# The proposed lift tables act as the exact Fi22 generators

The checked coordinate identities cover every `Option (Fin 3510)` value,
including the extra letter 15181. The existing Fi22 cycle-table comparison
identifies their right-hand sides with the literal ATLAS generators. Membership
of these proposed lift tables in the actual Fi23 group is a separate obligation.

Source: GLS3 Table 5.3u and the retained simultaneous matching in `ImageData`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate

theorem liftA_points (i : Option (Fin 3510)) :
    liftA (ImageData.point i) = ImageData.point (Option.map Fi22.generatorA i) := by
  have h := (action_checks (finSuccEquivLast.symm i)).1
  cases i <;> simpa only [Equiv.apply_symm_apply, Option.map_none, Option.map_some,
    Fi22.KernelCertificate.generatorA_apply_eq_fastA] using h

theorem liftB_points (i : Option (Fin 3510)) :
    liftB (ImageData.point i) = ImageData.point (Option.map Fi22.generatorB i) := by
  have h := (action_checks (finSuccEquivLast.symm i)).2
  cases i <;> simpa only [Equiv.apply_symm_apply, Option.map_none, Option.map_some,
    Fi22.KernelCertificate.generatorB_apply_eq_fastB] using h

end Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
