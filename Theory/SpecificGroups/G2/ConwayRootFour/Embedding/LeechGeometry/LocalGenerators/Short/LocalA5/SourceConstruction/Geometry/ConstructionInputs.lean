module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Inputs
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.CubicPlacement

/-!+# The remaining A₅ extension and fusion obligations

The source subgroup K₂ contains X, the central cubic of the long SL₃,
and a reflection acting as the graph element. `A5Placement` asks for this
actual subgroup of the common Leech centralizer, without any involution-class
assumption. Its cubic is the already constructed `longCubic`, so neither its
existence nor its action is a new geometric premise. Single-coordinate tests
suffice for the reflection. No equality with the arbitrary `L.swap` is required.

The independent fusion argument must identify `A5Placement.involution` with
the actual scalar involution. `Geometry.lean` consumes that conjugacy and
extends the reflection tests to construct the published geometric contract.
No inhabitant of `A5Placement` and no conjugacy are asserted here.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
using the D₁₀ centralizer in Lemma 47.2 and its placement by Lemma 48.8.
-/

open Atlas.Conway
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals

/-- The actual A₅ extension of the placed central cubic. Its involution class
is deliberately left to a separate source argument. -/
structure A5Placement (L : LongFrame) where
  subgroup : Subgroup LeechCentralQuotient
  alternating : subgroup ≃* alternatingGroup (Fin 5)
  le_centralizer : subgroup ≤ localCentralizer L
  cubic_le : (longCubic L).range ≤ subgroup
  reflection : subgroup
  reflection_on_single : ∀ j a,
    quotientModTwoRepresentation (reflection : LeechCentralQuotient)
        (L.coordinates (Pi.single j a)) =
      L.coordinates (action graph (Pi.single j a))

variable {L : LongFrame}

/-- A specified involution permits the fusion branch to run independently
of constructing a placement. A₅ fusion makes the choice immaterial. -/
def A5Placement.involution (P : A5Placement L) : P.subgroup :=
  P.alternating.symm scalarModelInvolution

theorem A5Placement.involution_order (P : A5Placement L) :
    orderOf P.involution = 2 := by
  rw [A5Placement.involution, P.alternating.symm.orderOf_eq]
  exact scalarModelInvolution_order

/-- Additivity extends the graph tests to the exact pair representation. -/
theorem A5Placement.reflection_action (P : A5Placement L) (v : Fin 6 → F) :
    quotientModTwoRepresentation (P.reflection : LeechCentralQuotient)
        (L.coordinates v) =
      L.coordinates (pairRepresentation (flip, flip) v) := by
  rw [graph_action]
  exact equivariant_of_single _ _ _ P.reflection_on_single v

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
