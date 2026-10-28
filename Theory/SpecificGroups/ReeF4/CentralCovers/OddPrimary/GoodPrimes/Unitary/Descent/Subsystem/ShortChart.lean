module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Coordinates
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Curve
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Negative
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Positive

/-!
# The faithful short-A₂ subgroup on the literal F₄ Geck lattice

The explicit invertible chart intertwines all four signed elementary SL3
root groups with the actual F4 short-root curves. The faithful block action
therefore gives a faithful marked homomorphism of SL3 into the root-generated
F4 cover. The positive and negative sparse coordinate checks discharge the
coordinate premise of `SourceBlocks.sourceModelOfChart`.

Source: GLS3 §2.6.2, the short A₂ subsystem in the common F₄ lattice.
-/

public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
open scoped Matrix
open TwistedE6.FoldedSubsystem.F4Identification
open ComplementRepresentation.ShortA2 SourceBlocks
variable (F : Type*) [Field F] [CharP F 2]

/-- Both signs and both short nodes act through the actual Geck root curves. -/
theorem chart_intertwines : Intertwines F (chart F) := by
  intro s k t v
  funext x
  obtain ⟨r, rfl⟩ := basisCoordinates.surjective x
  have hv : chart F v = toCoords F v ∘ basisCoordinates.symm := by
    funext y
    obtain ⟨i, rfl⟩ := basisCoordinates.surjective y
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using chart_apply F v i
  change chart F (action F (modelGenerator F s k t) v) (basisCoordinates r) =
    ((coverSimple F s (if k then 2 else 3) t).val.val *ᵥ chart F v) (basisCoordinates r)
  rw [chart_apply, hv, Coefficients.coverSimple_mulVec]
  cases s
  · exact negative_coordinates F k t v r
  · exact positive_coordinates F k t v r

/-- The faithful SL3 subgroup given by the characteristic-two short-root chart. -/
def sourceModel : Matrix.SpecialLinearGroup (Fin 3) F →* Cover F :=
  sourceModelOfChart F (chart F) (chart_intertwines F)

theorem sourceModel_injective : Function.Injective (sourceModel F) :=
  sourceModelOfChart_injective F (chart F) (chart_intertwines F)

@[simp] theorem sourceModel_generator (s k : Bool) (t : F) :
    sourceModel F (modelGenerator F s k t) = coverSimple F s (if k then 2 else 3) t :=
  sourceModelOfChart_generator F (chart F) (chart_intertwines F) s k t

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
