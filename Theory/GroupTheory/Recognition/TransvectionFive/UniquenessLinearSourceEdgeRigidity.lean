module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceEdgeStructure
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSystem
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearRecognition

/-!
# Rigidity and comparison assembly for the linear source system

The edge-fixer calculation gives the exact local rigidity hypothesis in
Theorem 37.9. Consequently every similarity of the literal linear source
system with the native binary matrix system is an equivalence. The constructor
below retains the literal source point, local normalizer and collinearity graph;
only the ambient generation and similarity remain explicit source premises.

Source: Aschbacher, *Sporadic Groups* (1994), 37.9 and 41.4--41.6,
pp.206, 222.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open SourceGeometry GraphUniquenessSystem GraphUniquenessSystem.Cosets
open BinaryLinear.TransvectionFiveLocal

universe u
variable {G : Type u} [Group G] [Finite G] {z : G}
variable (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

/-- The source uniqueness-system edge fixer has the checked odd-index rigidity.
The rewrites expose the literal point and chosen line of the source system. -/
theorem system_edge_rigid
    (hgen : rowNormalizer F ⊔ sourceThreeSpaceNormalizer F = ⊤) :
    AutomorphismRigid ((system_of_global_generation F hlinear hgen).H.subgroupOf
      (system_of_global_generation F hlinear hgen).edgeGroup) := by
  have hB : (system_of_global_generation F hlinear hgen).edgeGroup =
      edgeGroup F hlinear := by
    exact (system_edgeGroup_eq_line_kernel F hlinear hgen).trans
      (edgeFixer_eq_line_kernel F hlinear).symm
  have hH : (system_of_global_generation F hlinear hgen).H =
      sourceThreeSpaceNormalizer F := system_of_global_generation_local F hlinear hgen
  rw [hH, hB]
  exact edge_plane_automorphismRigid F hlinear

/-- Rigidity upgrades any compatible source/model similarity to an equivalence. -/
theorem isEquivalence_of_similarity
    (hgen : rowNormalizer F ⊔ sourceThreeSpaceNormalizer F = ⊤)
    (s : Similarity (system_of_global_generation F hlinear hgen)
      nativeSystem.system) : s.IsEquivalence :=
  s.isEquivalence_of_rigid (system_edge_rigid F hlinear hgen)

/-- Assemble a `SourceComparison` from the literal source system and a
similarity. Every source field is discharged by its literal construction; the
only external input is the compatible similarity itself. -/
def sourceComparison_of_similarity
    (hgen : rowNormalizer F ⊔ sourceThreeSpaceNormalizer F = ⊤)
    (s : Similarity (system_of_global_generation F hlinear hgen)
      nativeSystem.system) : SourceComparison F :=
  { source := system_of_global_generation F hlinear hgen
    source_point := system_of_global_generation_point F hlinear hgen
    source_local := system_of_global_generation_local F hlinear hgen
    source_graph := system_graph_adj_iff F hlinear hgen
    similarity := s
    equivalent := isEquivalence_of_similarity F hlinear hgen s }


end Theory.GroupTheory.TransvectionFive.UniquenessLinear
