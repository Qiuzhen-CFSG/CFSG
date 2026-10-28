module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.MarkedLattices.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.MarkedLattices.Reduction
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.MarkedLattices.Trace

/-!
# Assembly of marked ordinary lattice flags

An arbitrary ordinary lattice supplies an initial composition flag. Lattice
selection can then use an occurrence of any incident simple to choose a new
lattice with that simple socle. Applying the composition-factor theorem again
to the new lattice gives the required marked flag.

This is an assembly step for Feit I.17.12 and the construction on p.279.
The composition-factor and lattice-selection theorems remain explicit inputs;
their existence is not inferred from projectivity of the tree's edge objects.
-/

public section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules

open ModularBlock.PrimeBlockConstruction

variable {K G : Type*} [Field K] [Group G] [Finite G]
    {p m n : ℕ} [Fact p.Prime] {d : PrimeCongruenceBlockData p G}
    {L : CyclicRootLift K m}

/-- Discharge the occurrence premise of lattice selection using an initial
ordinary lattice, then construct a composition flag of the selected lattice.
All lattices use d's localization and the same residue map r. -/
theorem exists_vertexFlags_of_selection
    (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (flags : ∀ (v : {i // i ∈ d.block}) (X : OrdinaryLattice d v.val),
      Nonempty (IncidentFlag t r v X))
    (select : ∀ (v : {i // i ∈ d.block}) (X : OrdinaryLattice d v.val),
      IncidentFlag t r v X → ∀ e : ↥(t.incident v), Nonempty (MarkedLattice t r v e)) :
    Nonempty (∀ v : {i // i ∈ d.block}, VertexFlags t r v) := by
  apply exists_vertexFlags_of_markedLattices t r _ flags
  intro v e
  obtain ⟨X⟩ := exists_ordinaryLattice d v.val
  exact select v X (flags v X).some e

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
