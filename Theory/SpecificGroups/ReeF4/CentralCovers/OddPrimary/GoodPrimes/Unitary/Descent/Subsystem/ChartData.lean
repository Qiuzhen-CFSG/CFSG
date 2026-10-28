module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.Intertwining
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.SourceModel.Transport

/-!
# Application of the concrete short-root chart

The signed cover generators in `SourceBlocks` are literally the marked short
root curves used here. The checked matrix chart therefore supplies the faithful
short factor, and `dataOfShortMap` constructs the complete A₂ × A₂ subsystem.
This leaf bridges the original 52-dimensional representation to actual
algebraic F₄ points; it preserves the original elementary parameters.
Source: GLS3 §2.6.2 and Example 2.6.3.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
open TwistedE6.FoldedSubsystem.F4Identification WordDescent
variable {F : Type*} [Field F]

theorem chart_matrix_marking (e : SourceBlocks.Space F ≃ₗ[F] SourceBlocks.GeckSpace F)
    (he : SourceBlocks.Intertwines F e) (s k : Bool) (t : F) :
    SourceBlocks.matrixHom F e (simpleGenerator s k t) =
      F4Chevalley.rootCurve (signedRoot s (shortRoot k)) t := by
  rw [show simpleGenerator s k t = modelGenerator F s k t from rfl,
    SourceBlocks.matrixHom_generator F e he]
  cases s <;> cases k <;> rfl

variable [IsAlgClosed F] [CharP F 2]

/-- Application of the actual matrix chart to the two-factor construction. -/
def dataOfChart (e : SourceBlocks.Space F ≃ₗ[F] SourceBlocks.GeckSpace F)
    (he : SourceBlocks.Intertwines F e) (m : ℕ) : SubsystemData m F :=
  dataOfShortMap (pointMap (SourceBlocks.matrixHom F e) (chart_matrix_marking e he))
    (pointMap_marked _ (chart_matrix_marking e he))
    (pointMap_injective _ (chart_matrix_marking e he) (SourceBlocks.matrixHom_injective F e)) m

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
