module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.FixedDescent
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.MatrixDiagonal

/-!
# The concrete Suzuki-side Ree seed projection

The faithful four-dimensional representation of the whole split middle-node
Levi has the prescribed exceptional graph. Faithfulness ensures that every
diagonal element lifts to a fixed Levi element. The matrix diagonal calculation
identifies its image with the concrete Suzuki subgroup, giving an actual
equivalence of the fixed Levi with `SuzukiMatrixGroup m`.

Composing this equivalence with the seed's Levi retraction gives the surjective
`projection`, whose kernel is exactly the root-defined `seedRadical d .suzuki`.
There are no remaining matrix comparison hypotheses. The construction works
for every parameter, in particular for the large Ree groups with `m ≥ 1`.
Identifying the radical with the two-core remains a separate calculation.

Source: Aschbacher–Smith F.1.12(I)(5), printed p.263 (PDF p.274).
-/

@[expose] public noncomputable section

namespace ReeF4.LargeLocalSeeds

open BenderSuzuki.MatrixGroups
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open MaximalSubgroups.CommutingComponents.CarrierIdentification

namespace SuzukiLeviProjection

variable {m : ℕ}

/-- The actual fixed middle-node Levi is the concrete Suzuki matrix group. -/
def fixedLeviEquivSuzuki (d : LocalBlockInput m) :
    fixedLevi d .suzuki ≃* SuzukiMatrixGroup m :=
  fixedLeviEquivOfMatrixGraph d (SplitRepresentation.splitLeviRepresentation m)
    (SplitRepresentation.splitLeviRepresentation_injective m)
    (SplitRepresentation.pairedMap_range d) (MatrixDiagonal.pairedDiagonal_eq_suzuki m)

/-- The identification retains the literal four-dimensional matrix action. -/
@[simp] theorem fixedLeviEquivSuzuki_val (d : LocalBlockInput m)
    (x : fixedLevi d .suzuki) :
    (fixedLeviEquivSuzuki d x).val =
      SplitRepresentation.splitLeviRepresentation m (forgetToSplitLevi d x) := rfl

/-- The Suzuki projection of the root-defined fixed seed. -/
def projection (d : LocalBlockInput m) :
    standardSeed d .suzuki →* SuzukiMatrixGroup m :=
  (fixedLeviEquivSuzuki d).toMonoidHom.comp (projectionToLevi d)

theorem projection_surjective (d : LocalBlockInput m) :
    Function.Surjective (projection d) :=
  (fixedLeviEquivSuzuki d).surjective.comp (projectionToLevi_surjective d)

/-- The kernel is the radical as a subgroup of the seed, not of the ambient group. -/
theorem projection_ker (d : LocalBlockInput m) :
    (projection d).ker = seedRadical d .suzuki :=
  projectionOfMatrixGraph_ker d (SplitRepresentation.splitLeviRepresentation m)
    (SplitRepresentation.splitLeviRepresentation_injective m)
    (SplitRepresentation.pairedMap_range d) (MatrixDiagonal.pairedDiagonal_eq_suzuki m)

/-- On the fixed Levi, the projection is its concrete Suzuki identification. -/
@[simp] theorem projection_fixedLeviInclusion (d : LocalBlockInput m)
    (x : fixedLevi d .suzuki) :
    projection d (fixedLeviInclusion d .suzuki x) = fixedLeviEquivSuzuki d x := by
  change fixedLeviEquivSuzuki d (projectionToLevi d (fixedLeviInclusion d .suzuki x)) = _
  rw [projectionToLevi_inclusion]

end SuzukiLeviProjection

/-- Every concrete Suzuki-side seed surjects onto the Suzuki matrix group with
exactly the specified radical as kernel; in particular this holds for `m ≥ 1`. -/
theorem exists_suzukiSeedProjection {m : ℕ} (d : LocalBlockInput m) :
    ∃ π : standardSeed d .suzuki →* SuzukiMatrixGroup m,
      Function.Surjective π ∧ π.ker = seedRadical d .suzuki :=
  ⟨SuzukiLeviProjection.projection d, SuzukiLeviProjection.projection_surjective d,
    SuzukiLeviProjection.projection_ker d⟩

end ReeF4.LargeLocalSeeds
