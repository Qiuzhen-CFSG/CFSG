module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.ImageAMembership
/-! The first matrix is an involution; its inverse image table is identical. -/
@[expose] public section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Lattices
theorem imageAInvVectors_mem (j : Fin 37) : vectorOfData (imageAInvVectors j) ∈ leech :=
  imageAVectors_mem j
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
