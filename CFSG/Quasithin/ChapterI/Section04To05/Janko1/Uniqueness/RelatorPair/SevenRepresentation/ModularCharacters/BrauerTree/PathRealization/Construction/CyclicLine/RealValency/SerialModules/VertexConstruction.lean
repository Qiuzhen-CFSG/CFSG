module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.Contracts

/-!
# Assembly of serial vertex reductions from marked composition flags

The supplied flags use actual lattices at `b.data.primeIdeal`, reduced by
`r.residue`, and the tree with the root lift `principalBlock_rootLift b r`.
Exclusion of competing upper covers turns these flags into exhaustive
ascending series without changing their quotient actions or factor labels.

Two source obligations remain explicit: constructing the marked simple-socle
lattices (Feit I.17.12, applied on p.279), and proving the cover and successor
exclusions (VII.8.1--2 and the proofs of VII.2.20 and VII.2.23, pp.302--303).
These conditional applications do not assert their existence. In particular
`Tree.projective` alone does not identify principal indecomposable modules
or their socles, and a lift over a complete coefficient ring is not silently
substituted for a lattice over the specified localization.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine
open RealValency.SerialModules

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- Once both source obligations are proved, the finite-filtration argument
produces the requested exhaustive series for every ordinary vertex. -/
public theorem principalBlock_vertexSeries_exists_of_flags
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (a : ∀ v : {i // i ∈ b.data.block}, VertexFlags t r v)
    (hcover : ∀ v, (a v).UniqueCovers) (hnext : ∀ v, (a v).ConsecutiveUnique)
    (v : {i // i ∈ b.data.block}) :
    ∃ c : VertexSeries t r v, c.ConsecutiveUnique :=
  ⟨(a v).toVertexSeries (hcover v),
    (a v).toVertexSeries_consecutiveUnique (hcover v) (hnext v)⟩

/-- On the literal residue representation, the marked first subspace is the
specified edge module and prevents a decomposition into two nonzero summands.
This is the simple-socle consequence used before the seriality argument. -/
public theorem principalBlock_vertexFlags_socle_and_indecomposable
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (v : {i // i ∈ b.data.block}) (a : VertexFlags t r v)
    (e : ↥(t.incident v)) (h : 0 < (t.incident v).card) :
    Nonempty (((a.flag e).term (⟨0, h⟩ : Fin (t.incident v).card).succ).toRepresentation.Equiv
      (t.rep e.val)) ∧
      ∀ U W : Subrepresentation ((a.lattice e).reduction r),
        IsCompl U W → U = ⊥ ∨ W = ⊥ :=
  ⟨a.socle_equiv e h, a.no_nontrivial_complement e⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
