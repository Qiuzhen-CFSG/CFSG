module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Descent
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.MatrixData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization

/-!
The explicit matrix group has a faithful integral realization in Co₀ and a
surjective comparison with SL₃(4) whose kernel is exactly its scalar signs.
Transport through the range equivalence constructs the unconditional
`latticeBlock`. Its A₄ marking has the actual rational scalar image in the
retained A₅, and the projected cover commutes with this marked subgroup.

The cover is the literal range of `matrixToLeech`. Its matrix equivalence,
quotient evaluation, and descended generator formulas remain available for
the graph-normalizer construction. The integral cover is not assumed to split.

Source: Aschbacher, Sporadic Groups (1994), 49.2 and the SL₃(4) construction
in 49.5, pp.280 and 283. In particular, 48.3 alone supplies only PSL₃(4)
in the Suzuki ambient group. MatrixData cites the explicit ATLAS candidate.
-/

@[expose] public noncomputable section
open Matrix Atlas.Conway Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block

variable (marking : alternatingGroup fourPoints →* alternatingGroup (Fin 5))
  (hmarking : Function.Injective marking)
  (ρ : matrixGroup →* LeechIsometryGroup) (hρ : Function.Injective ρ)
  (hρsign : leechCentralSigns.comap ρ = matrixSigns)
  (hcomm : ∀ a g, Commute (scalarFive (marking a)) (leechCentralProjection (ρ g)))
  (q : matrixGroup →* SL(3,F)) (hq : Function.Surjective q)
  (hqker : q.ker = matrixSigns)

/-- Assemble the two independent comparisons of the concrete matrix group.
The integral subgroup is exactly the range of the supplied faithful realization. -/
def latticeBlockOfMatrix : LatticeBlock where
  marking := marking
  marking_injective := hmarking
  cover := ρ.range
  quotient := q.comp (MonoidHom.ofInjective hρ).symm.toMonoidHom
  surjective := hq.comp (MonoidHom.ofInjective hρ).symm.surjective
  kernel := by
    ext g
    change q ((MonoidHom.ofInjective hρ).symm g) = 1 ↔ g.val ∈ leechCentralSigns
    rw [← MonoidHom.mem_ker, hqker, ← hρsign]
    change ρ ((MonoidHom.ofInjective hρ).symm g) ∈ leechCentralSigns ↔ _
    rw [MonoidHom.apply_ofInjective_symm]
  commute := by
    intro a g
    have h := hcomm a ((MonoidHom.ofInjective hρ).symm g)
    simpa only [MonoidHom.apply_ofInjective_symm] using h

/-- The integral quotient retains the supplied matrix-group comparison. -/
theorem latticeBlockOfMatrix_quotient (g : matrixGroup) :
    (latticeBlockOfMatrix marking hmarking ρ hρ hρsign hcomm q hq hqker).quotient
      (ρ.rangeRestrict g) = q g := by
  change q ((MonoidHom.ofInjective hρ).symm ((MonoidHom.ofInjective hρ) g)) = q g
  rw [MulEquiv.symm_apply_apply]

/-- The descended block has precisely the prescribed integral lifts. This is
an application to the actual `LatticeBlock.block` consumed by the graph owner. -/
theorem latticeBlockOfMatrix_block (g : matrixGroup) :
    (latticeBlockOfMatrix marking hmarking ρ hρ hρsign hcomm q hq hqker).block (q g) =
      leechCentralProjection (ρ g) := by
  rw [← latticeBlockOfMatrix_quotient marking hmarking ρ hρ hρsign hcomm q hq hqker g]
  exact LatticeBlock.block_quotient _ _

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long

/-- The integral Leech block with exact central-sign quotient SL₃(4),
centralizing the marked scalar A₄ after projection to the Conway quotient. -/
def latticeBlock : LatticeBlock :=
  Block.latticeBlockOfMatrix Block.matrixMarking Block.matrixMarking_injective
    Block.matrixToLeech Block.matrixToLeech_injective Block.matrixToLeech_signs
    Block.matrixToLeech_commute Block.matrixQuotient Block.matrixQuotient_surjective
    Block.matrixQuotient_ker_eq_matrixSigns

@[simp] theorem latticeBlock_marking : latticeBlock.marking = Block.matrixMarking := rfl

/-- The cover is the actual image of the displayed integral matrix action. -/
theorem latticeBlock_cover : latticeBlock.cover = Block.matrixToLeech.range := rfl

/-- Concrete matrix coordinates on the integral cover, retained for its normalizer. -/
def Block.matrixCoverEquiv : Block.matrixGroup ≃* latticeBlock.cover :=
  MonoidHom.ofInjective Block.matrixToLeech_injective

@[simp] theorem Block.matrixCoverEquiv_apply (g : Block.matrixGroup) :
    (Block.matrixCoverEquiv g).val = Block.matrixToLeech g := rfl

/-- The cover quotient is the proved restriction of modular matrix reduction. -/
@[simp] theorem latticeBlock_quotient (g : Block.matrixGroup) :
    latticeBlock.quotient (Block.matrixCoverEquiv g) = Block.matrixQuotient g :=
  Block.latticeBlockOfMatrix_quotient _ _ _ _ _ _ _ _ _ g

/-- The actual descended block has the specified integral matrix lifts. -/
theorem latticeBlock_block (g : Block.matrixGroup) :
    latticeBlock.block (Block.matrixQuotient g) =
      leechCentralProjection (Block.matrixToLeech g) :=
  Block.latticeBlockOfMatrix_block _ _ _ _ _ _ _ _ _ g

/-- First generator formula, with the literal field comparison and central projection. -/
theorem latticeBlock_block_generatorA :
    latticeBlock.block (SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom Block.threeA) =
      leechCentralProjection (Block.matrixToLeech Block.matrixGeneratorA) := by
  rw [← Block.matrixQuotient_generatorA]
  exact latticeBlock_block _

/-- Second generator formula in the same matrix and quotient conventions. -/
theorem latticeBlock_block_generatorB :
    latticeBlock.block (SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom Block.threeB) =
      leechCentralProjection (Block.matrixToLeech Block.matrixGeneratorB) := by
  rw [← Block.matrixQuotient_generatorB]
  exact latticeBlock_block _

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
