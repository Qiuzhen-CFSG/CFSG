module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Setup
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Octonion

/-!
# The remaining lattice-generator construction

These are the generator relations used to construct K₁ in Aschbacher,
*Sporadic Groups* (1994), Lemma 49.5, p.283, following Section 48, p.269.
They retain a genuine injective SL₃(4) homomorphism into the Leech central
quotient and its graph involution. The tetrahedral marking may be any injective
marking in the actual scalar A₅. `Long.Subgroup` proves extension to the actual
octonion subgroup and transport to the specified `I`.

No inhabitant is asserted here. Constructing these lattice isometries remains
a separate obligation; the existing commuting J₂ image does not discharge it.
-/

@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
open Matrix Atlas.SplitOctonion Atlas.Conway
open scoped MatrixGroups
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization

/-- Lattice generators before choosing the five-point tetrahedral marking.
The relation uses the actual octonion graph convention. No map on `longLocal`
and no coordinate intertwiner is included. -/
structure GeneratorData where
  marking : alternatingGroup fourPoints →* alternatingGroup (Fin 5)
  marking_injective : Function.Injective marking
  block : SL(3,F) →* LeechCentralQuotient
  block_injective : Function.Injective block
  swap : LeechCentralQuotient
  swap_square : swap * swap = 1
  swap_not_block : swap ∉ block.range
  swap_block : ∀ A, swap * block A = block (graphTwist A) * swap
  block_commute : ∀ a A, Commute (scalarFive (marking a)) (block A)
  swap_commute : ∀ a, Commute (scalarFive (marking a)) swap

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
