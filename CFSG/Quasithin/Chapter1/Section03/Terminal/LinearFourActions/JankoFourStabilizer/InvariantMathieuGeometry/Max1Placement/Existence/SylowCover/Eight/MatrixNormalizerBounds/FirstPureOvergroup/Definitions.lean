module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Definitions
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets.Orbit

/-!
# Trace-image geometry for the first pure Sylow eight

The trace operator is the sum of the actions of all elements of the literal
subgroup `U 0`. Its image is preserved by the full ambient normalizer, by
reindexing this sum under conjugation. A small image can therefore produce
a proper geometric overgroup without identifying an ambient maximal subgroup.

The specified plane and local word below are certificate inputs. Their
definitions alone assert no trace-image equality or stabilizer membership.
The first plane vector is the existing max1 fixed vector, in the unchanged
ATLAS row convention. The other vector and the word were discovered from
`SylowNormalEights/source/matrix-witness.json` and the actual max1 tables.

Source context: the J₄ Sylow-overgroup analysis invoked by Aschbacher–Smith,
`refs/quasithin.pdf`, printed pp.47–48. Matrix and local-word attribution is
retained in `Model.Data` and `Cardinality.Subgroup`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.Cardinality

/-- The subgroup trace, using every element of the actual first row once. -/
noncomputable def firstPureTrace (v : CosetVector) : CosetVector := by
  letI := Fintype.ofFinite (U 0)
  exact ∑ u : U 0, vectorRight v (u : Model)

/-- The second vector of the proposed trace image, in original coordinates. -/
def firstPureSecondVector : CosetVector :=
  fun j => if (3683754961113342797877254413953002 : ℕ).testBit j.val then 1 else 0

/-- The four vectors of the proposed binary plane. -/
def firstPurePlaneVector (i : Fin 4) : CosetVector :=
  ![0, cosetBaseVector, firstPureSecondVector, cosetBaseVector + firstPureSecondVector] i

/-- A literal set of four row vectors; trace-image equality is a separate certificate. -/
def firstPurePlane : Set CosetVector := Set.range firstPurePlaneVector

/-- Setwise stabilizer for the right row action, retaining both directions. -/
def firstPurePlaneStabilizer : Subgroup Model where
  carrier := {g | ∀ v, vectorRight v g ∈ firstPurePlane ↔ v ∈ firstPurePlane}
  one_mem' := by intro v; rw [vectorRight_one]
  mul_mem' := by
    intro g h hg hh v
    rw [vectorRight_mul, hh, hg]
  inv_mem' := by
    intro g hg v
    have h := hg (vectorRight v g⁻¹)
    simpa only [← vectorRight_mul, inv_mul_cancel, vectorRight_one] using h.symm

/-- A short word carrying the proposed plane to a plane fixed by local X. -/
noncomputable def firstPureTransportWord : Model :=
  let x : Model := localX matrixA_mul_self matrixB_pow_four
  let y : Model := localY matrixA_mul_self matrixB_pow_four
  x * y * y * x * y * x * y * y

/-- Candidate element of the plane stabilizer outside the eight normalizer. -/
noncomputable def firstPureStrictWitness : Model :=
  firstPureTransportWord * (localX matrixA_mul_self matrixB_pow_four : Model) *
    firstPureTransportWord⁻¹

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
