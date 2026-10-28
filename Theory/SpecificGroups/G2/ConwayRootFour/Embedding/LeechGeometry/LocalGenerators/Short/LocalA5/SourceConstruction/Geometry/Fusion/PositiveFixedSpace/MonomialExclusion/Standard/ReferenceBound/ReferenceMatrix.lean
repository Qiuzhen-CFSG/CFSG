module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Data

/-!
# The reference action matrix

The flat-coordinate sign and pullback of the first marked quaternion generator
are checked against their literal definitions. Kernel reduction then checks its
binary matrix against the reciprocal-basis formula. All later certificates can
reuse this one calculation; they do not repeat the lattice-basis verification.

The integers were computed from the existing diagnostic script and are verified
here. Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

open Atlas.Codes
open scoped Matrix
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

def referenceRows : Fin 24 → ℕ := ![1,13,5,6,68,122,21,227,1028,1803,261,2828,5714,51673,22860,30449,66876,855141,328954,396196,4473943,8036470,1400043,14914235]

def referenceTable : Matrix (Fin 24) (Fin 24) Bit := fun i => maskBit (referenceRows i)

def referencePullTable : Fin 24 → Fin 24 := ![2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13,18,19,16,17,22,23,20,21]

set_option Elab.async false in
theorem referenceSign_table :
    (fun i => jWord referenceHexB (StandardCoordinates.flat.symm i)) = maskBit 13027014 := by
  decide +kernel

set_option Elab.async false in
theorem referencePull_table :
    (fun i => StandardCoordinates.flat (referencePullA (StandardCoordinates.flat.symm i))) =
      referencePullTable := by decide +kernel

set_option Elab.async false in
theorem referenceMatrix_table : referenceMatrix = referenceTable := by
  unfold referenceMatrix
  rw [referenceSign_table, referencePull_table]
  decide +kernel

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
