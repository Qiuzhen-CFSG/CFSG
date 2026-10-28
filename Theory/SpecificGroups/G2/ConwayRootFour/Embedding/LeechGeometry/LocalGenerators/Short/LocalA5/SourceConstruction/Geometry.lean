module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Inputs
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.ConstructionInputs

/-!
# Assembly of the marked local Leech geometry

The central cubic of any long frame is already placed in the literal
centralizer of I and D₁₀. Once an A₅ extension is constructed, its inclusion
supplies the full cubic family; additive extension supplies the reflection
action. A single independently proved scalar-class conjugacy supplies the
marking. These are the two remaining source premises, not existence claims.

The unconditional `exists_geometry` remains the final assembly obligation
after constructing `A5Placement` and proving its involution fusion.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
using Lemmas 47.2 and 48.8. The consumer is `SourceConstruction.lean`.
-/

open Atlas.Conway
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
variable {L : LongFrame}

/-- Assemble every clause of the published geometric input from the actual
A₅ extension and its separately established scalar fusion. -/
def geometryOfPlacement (P : A5Placement L)
    (hclass : IsConj (P.involution : LeechCentralQuotient) scalarInvolution) :
    Geometry L where
  subgroup := P.subgroup
  alternating := P.alternating
  mem a := (P.le_centralizer a.property).1
  centralizes a d := by
    have h := (P.le_centralizer a.property).2 (dihedralLift L d) ⟨d, rfl⟩
    exact h.symm
  reflection := P.reflection
  reflection_action := P.reflection_action
  cubic t := ⟨longCubic L t, P.cubic_le ⟨t, rfl⟩⟩
  cubic_action := longCubic_action L
  scalar_witness := ⟨P.involution, P.involution_order, hclass⟩

/-- The actual consumer of the cubic-placement and fusion branches. Neither
of the remaining geometric premises is silently discharged. -/
theorem exists_geometry_of_placement (L : LongFrame) (P : A5Placement L)
    (hclass : IsConj (P.involution : LeechCentralQuotient) scalarInvolution) :
    Nonempty (Geometry L) := ⟨geometryOfPlacement P hclass⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
