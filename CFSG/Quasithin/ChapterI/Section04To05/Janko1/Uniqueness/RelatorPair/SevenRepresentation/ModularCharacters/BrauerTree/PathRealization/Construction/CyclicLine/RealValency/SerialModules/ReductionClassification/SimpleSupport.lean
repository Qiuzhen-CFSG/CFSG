module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.SimpleSupport

/-!
# Simple support at the actual principal eleven-block prime

Every simple submodule of an ordinary vertex reduction is equivalent to an
incident edge, using the supplied vertex series. The comparison uses exactly
`Localization.AtPrime b.data.primeIdeal` and `r.residue` through the ordinary
lattice API. Neither the arbitrary reduction's indecomposability nor seriality
is assumed. Once the tree and series are supplied, no additional group-order
or model fact is needed.

Source: Feit I.17, VII.2.19 and the simple-submodule step of VII.2.25,
printed p.304. This discharges `SimpleSupport` in the reduction classification;
`CommonSimpleRigidity` remains the separate assembly owner's obligation.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine
open RealValency.SerialModules RealValency.SerialModules.ReductionClassification

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- Constituent support for all ordinary lattices at the literal eleven-block
vertex, with the earlier-source vertex series supplied explicitly. -/
public theorem principalBlock_simpleSupport
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (v : {i // i ∈ b.data.block}) (a : VertexSeries t r v) :
    SimpleSupport t r v :=
  simpleSupport_of_vertexSeries a (by decide)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
