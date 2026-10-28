module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Generators
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Descent
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph

/-!
# Concrete lattice generators for the long local subgroup

The faithful integral realization of the explicit Eisenstein matrix group has
exact central-sign quotient SL₃(4). Its quaternion graph normalizer has square
minus identity and induces the precise Peirce action J A⁻ᵀ J. Both commute
with the marked rational tetrahedral scalars in the retained Leech model.

Descending these concrete constructions gives every field of `GeneratorData`.
In particular, the descended block is injective and the graph involution lies
outside it because it inverts the nontrivial cubic center. No lattice witness
or other premise remains in `nonempty_generatorData`; the octonion extension
and transport to the specified scalar subgroup belong to `Long.Subgroup`.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long

/-- Assemble the original generator contract from actual integral block and
graph constructions, without assuming that the SL₃ block splits in Co₀. -/
theorem nonempty_generatorData_of_lattice (D : LatticeBlock) (S : LatticeGraph D) :
    Nonempty GeneratorData := ⟨S.generatorData⟩

/-- The concrete Leech block and its graph normalizer supply the original
long-generator contract, with no additional hypotheses. -/
theorem nonempty_generatorData : Nonempty GeneratorData :=
  nonempty_generatorData_of_lattice latticeBlock latticeGraph

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
