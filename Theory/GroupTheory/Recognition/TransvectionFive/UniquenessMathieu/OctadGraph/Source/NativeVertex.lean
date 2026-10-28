module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeRow
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.GeneratedSystem
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.GeneratedSystem

/-!
# Native vertex maps for the literal source uniqueness systems

Transport the kernel-marked source-row/native-octad isomorphism through the
actual equalities of vertex stabilizers in the two uniqueness systems. The
result retains the map on each row element and its full quotient action.
The original Mathieu fusion hypothesis supplies this map in the correctly
oriented normalizer-generated subgroup without extra structural assumptions.

This is the vertex-map component of Aschbacher, *Sporadic Groups* (1994),
41.4, printed p.222. It is not yet a similarity: the marked native edge and
plane restrictions and the compatible local-plane map remain obligations.
The private import is an intentional implementation extension of the source
system assembly, needed only to unfold its original-fusion wrapper.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer GraphUniquenessSystem GraphUniquenessSystem.Cosets
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

/-- The source vertex group is literally the same row normalizer. -/
def vertexRowEquiv (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    (system_of_generation F D hgen).vertexGroup ≃* rowNormalizer F :=
  MulEquiv.subgroupCongr (stabilizer_base _)

/-- The target vertex group is the actual stabilizer of the marked native octad. -/
def nativeVertexEquiv : OctadGraph.system.vertexGroup ≃* Stabilizer OctadGraph.first :=
  MulEquiv.subgroupCongr OctadGraph.system_vertex

/-- A vertex-group map between the literal systems. Its quotient action is
recorded, while the edge and local-group compatibility obligations stay explicit. -/
theorem exists_native_vertex_equiv
    (hgen : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    ∃ e : (system_of_generation F D hgen).vertexGroup ≃* OctadGraph.system.vertexGroup,
      (∀ a : F.row,
        nativeVertexEquiv (e ((vertexRowEquiv F D hgen).symm
          (inclusion F.row.le_normalizer a))) =
            ((coreCoordinates OctadGraph.first).symm (rowCoordinates F a) :
              Stabilizer OctadGraph.first)) ∧
      ∀ a, linearAction OctadGraph.first (nativeVertexEquiv (e a)) =
        rowAction F D (vertexRowEquiv F D hgen a) := by
  obtain ⟨e, he, hq⟩ := exists_native_row_equiv_action F D OctadGraph.first
  refine ⟨(vertexRowEquiv F D hgen).trans (e.trans nativeVertexEquiv.symm), ?_, ?_⟩
  · intro a
    simpa only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using he a
  · intro a
    simpa only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using hq (vertexRowEquiv F D hgen a)

/-- The genuine earlier fusion hypothesis supplies a native vertex isomorphism
for the actual oriented induction system, with no local structure callback. -/
theorem oriented_normalizerSpan_vertex_equiv (hfusion : F.MathieuFusion) :
    Nonempty ((oriented_normalizerSpan_system F hfusion).vertexGroup ≃*
      OctadGraph.system.vertexGroup) := by
  let E := SourceData.ofFusion F hfusion
  obtain ⟨e, _, _⟩ := exists_native_vertex_equiv (normalizerSpanMarking E.oriented.marking)
    (normalizerSpanLocalData E.oriented.marking E.localData)
    (normalizerSpan_pair_generate E.oriented.marking E.localData)
  exact ⟨e⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
