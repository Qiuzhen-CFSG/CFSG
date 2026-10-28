module

public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Isometry
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.LatticeGenerators.Reduction
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.LatticeGenerators.Natural

/-!
# Leech generator compatibility for the fixed source comparisons

The prescribed Golay–cocode map intertwines the source sign and permutation
formulas with the actual integral Leech isometries modulo twice the lattice.
The calculation applies to every coordinate pair and retains both corrections
in the sign formula. The fixed real comparison sends the positive halfspace
basis `L¹(x)` to the marked standard coordinate basis and intertwines the
actual `ψ₁(d)`, `ψ₂(d)`, and standard `ψ₁(α)` halfspace transports.

These are the lattice and natural-module generator calculations. Conjugation
on the triality quotient and assembly for the whole local group use them in
separate arguments.

Source: Aschbacher, *Sporadic Groups*, Lemma 23.10(4), pp. 120–121,
Lemma 27.4, pp. 146–147, and the generator comparison on p. 148.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- The fixed quadratic isometry intertwines every Golay sign generator. -/
theorem sourceLatticeComparison_sign (Y : golay) (x : QuadraticCoordinates) :
    sourceLatticeComparison (sourceSignCoordinates Y x) =
      leechModTwoRepresentation (signIsometry Y) (sourceLatticeComparison x) :=
  sourceCoordinateMap_sign Y x

/-- The fixed quadratic isometry intertwines every actual Golay coordinate permutation. -/
theorem sourceLatticeComparison_permutation (σ : Mathieu24CodeModel) (x : QuadraticCoordinates) :
    sourceLatticeComparison (sourcePermutationCoordinates σ x) =
      leechModTwoRepresentation (permutationEmbedding σ) (sourceLatticeComparison x) :=
  sourceCoordinateMap_permutation σ x

end Sporadic.Monster.Construction.LocalC
