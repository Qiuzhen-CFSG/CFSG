module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Complete
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.RowGeometry

/-!
# Applying the constructed local data to the source coset geometry

The source geometry's row-residue generation theorem requires the corrected
local boundary. Supply it using `SourceData.ofFusion` on the original marking.
Thus the two marked flag intersections generate the actual oriented row
normalizer with no local-data callback. The later source/model comparison and
ambient M₂₄ recognition remain with their geometry and recognition owners.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1, pp.219–220.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- Actual source-geometry application: the two original marked flag
intersections generate the oriented row normalizer. The graph producer's
`LocalData` premise is discharged by the source construction. -/
theorem oriented_row_flag_generate (hfusion : F.MathieuFusion) :
    let M := (SourceData.ofFusion F hfusion).oriented.marking
    (rowNormalizer M ⊓ planeNormalizer M) ⊔
      (rowNormalizer M ⊓ threeSpaceNormalizer M) = rowNormalizer M := by
  let D := SourceData.ofFusion F hfusion
  exact OctadSource.row_flag_generate D.oriented.marking D.localData

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
