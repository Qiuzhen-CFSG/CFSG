module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.Cycle

/-!
# Integral origins and the cyclic-series assembly at eleven

Every supplied ordinary vertex has an actual lattice over the localization
at `b.data.primeIdeal`. Its reduction is taken using the exact residue map in
`r`, which also defines `principalBlock_rootLift b r`.

The common cyclic successor can be constructed once serial vertex reductions,
the absence of branching between consecutive factors, and dual closure have
been proved. These source-module inputs remain explicit below; arbitrary
ordinary lattices do not establish them. The complete family existence
theorem remains an obligation of this module's assembly.

Source: Feit VII.2.20, VII.2.23 and VII.2.25 (pp.280, 302--304).
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine
open RealValency.SerialModules

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- Each actual ordinary vertex has a finite free lattice at the specified
prime. This theorem does not assert that an arbitrary reduction is serial. -/
public theorem principalBlock_vertexLattice_exists (b : PrincipalBlockIdentification d)
    (v : {i // i ∈ b.data.block}) : Nonempty (OrdinaryLattice b.data v.val) :=
  exists_ordinaryLattice b.data v.val

/-- Conditional source assembly with the literal prime, residue map, root lift,
tree and incident-edge subtype. All additional module premises remain visible. -/
public noncomputable def principalBlock_cyclicVertexFamily_of_series
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (v : {i // i ∈ b.data.block}) (a : VertexSeries t r v) (hc : a.ConsecutiveUnique)
    (hd : ∀ e, ∃ f, Nonempty (((a.lattice e).reduction r).dual.Equiv
      ((a.lattice f).reduction r))) : CyclicVertexFamily t r v :=
  cyclicVertexFamilyOfSeries a hc hd

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
