module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification

/-!
# Classification assembly at the actual principal eleven-block prime

The principal-vertex case is proved without any extra classification premise.
The conditional general theorem uses the supplied vertex series and the literal
localization, residue map, and root lift. Constituent support and common-simple
rigidity are still missing source results. They are independent of existence of
the supplied vertex series; no seriality hypothesis is imposed on the arbitrary
reduction. Final discharge of these two premises belongs in this module.

Source: Feit VII.2.25, printed p.280, reduction-level proof on p.304.
Exceptional multiplicity is one; the lattice affords exactly the ordinary
vertex character. The stronger integral-lattice isomorphism is not asserted.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine
open RealValency.SerialModules RealValency.SerialModules.ReductionClassification

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- The principal ordinary vertex has degree one, so every reduction belongs
to its supplied vertex family. No common-simple rigidity premise is needed. -/
public theorem principalBlock_principal_reduction_classification
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (a : VertexSeries t r ⟨b.data.principal, b.data.principal_mem⟩)
    (X : OrdinaryLattice b.data b.data.principal) :
    ∃ e : ↥(t.incident ⟨b.data.principal, b.data.principal_mem⟩),
      Nonempty ((X.reduction r).Equiv ((a.lattice e).reduction r)) := by
  apply classify_of_degree_one a (by decide) _ X
  rw [b.data.principal_eq, ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter_apply]

/-- Application of the exhaustive assembly with the exact prime, residue map
and module-valued tree. The two source-classification premises remain explicit. -/
public theorem principalBlock_reduction_classification_of_support_and_rigidity
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (v : {i // i ∈ b.data.block}) (a : VertexSeries t r v)
    (hs : SimpleSupport t r v) (hu : CommonSimpleRigidity t r v)
    (X : OrdinaryLattice b.data v.val)
    (hX : Module.IsIndecomposable (MonoidAlgebra ElevenClosure G) (X.reduction r).asModule) :
    ∃ e : ↥(t.incident v), Nonempty ((X.reduction r).Equiv ((a.lattice e).reduction r)) :=
  classify_of_simpleSupport_of_commonSimpleRigidity a (by decide) hs hu X hX

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
