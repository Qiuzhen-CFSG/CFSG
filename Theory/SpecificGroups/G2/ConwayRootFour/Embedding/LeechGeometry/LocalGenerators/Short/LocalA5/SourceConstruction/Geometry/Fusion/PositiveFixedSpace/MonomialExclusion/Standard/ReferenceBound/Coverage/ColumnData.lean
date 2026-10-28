module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.NormalForm

/-!
# Proposed involutive column permutations

This small table is original diagnostic output, using the literal marked maps
and the six ATLAS hexacode generators. It is deliberately independent of the
published signed-candidate table. Its exhaustiveness is the separate
`ColumnCoverage` obligation; no completeness assertion is encoded in the data.

Source context: the reference calculation for Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5, pp.283–284.
-/

open Atlas.Codes
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage

/-- Identity and fifteen proposed involutions, in `hexIndexEquiv` indexing. -/
def columnData : Vector (Fin 6 → Fin 6) 16 :=
  ⟨#[![0,1,2,3,4,5],
    ![0,1,4,5,2,3],
    ![0,2,1,4,3,5],
    ![0,3,2,1,5,4],
    ![0,4,5,3,1,2],
    ![0,5,3,2,4,1],
    ![1,0,2,5,4,3],
    ![1,0,4,3,2,5],
    ![2,1,0,3,5,4],
    ![2,3,0,1,4,5],
    ![3,1,5,0,4,2],
    ![3,4,2,0,1,5],
    ![4,1,3,2,0,5],
    ![4,5,2,3,0,1],
    ![5,1,2,4,3,0],
    ![5,2,1,3,4,0]], rfl⟩

def columnCandidate (q : Fin 16) (i : HexIndex) : HexIndex :=
  hexIndexEquiv.symm (columnData.get q (hexIndexEquiv i))

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage
