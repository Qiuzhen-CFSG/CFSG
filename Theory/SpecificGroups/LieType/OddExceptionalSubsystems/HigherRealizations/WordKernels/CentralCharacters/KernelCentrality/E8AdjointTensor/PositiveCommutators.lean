module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.SimpleCommutators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.PositiveCommutators.AbsentRoots

/-!
# Positive integral commutators for the E6 tensor in E8

The Cartan and opposite-simple cases use the signed normalization in
`SimpleCommutators`. For every other root coordinate, the sum-root theorem
supplies the exact source root-string coefficient, and the absent-root theorem
supplies zero. Thus the fixed source-route tensor intertwines each positive
E6 simple operator with the commutator by its actual E8 image.

This discharges the positive premise of
`KernelCentrality.e8IntegralAdjointData_of_positive_and_opposition`; the
independent opposition input and final data assembly stay with that consumer.
Source: GLS3 §§1.10–1.12 and 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`),
the common integral lattice for a closed root subsystem.
-/

public section
noncomputable section
open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
attribute [local instance] Classical.decEq
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- All six positive-simple identities hold on the literal 78-coordinate E6
source and 248-coordinate E8 target, with the fixed source route signs. -/
theorem positive_commutators : PositiveCommutators := by
  apply positiveCommutators_of_roots
  intro i r hopp
  by_cases h : typeE6RootPairing.root i + typeE6RootPairing.root r ∈
      Set.range typeE6RootPairing.root
  · obtain ⟨s, hs⟩ := h
    rw [eMatrix_mulVec_v_add hs, map_smul, adjointMap_single]
    exact (positive_root_commutator_add i r s hs).symm
  · exact positive_commutator_no_root i r hopp h

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
