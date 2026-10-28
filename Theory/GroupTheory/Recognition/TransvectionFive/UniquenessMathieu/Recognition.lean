module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.Graph

/-!
# Mathieu uniqueness from the measured local source data

This is the source-faithful boundary for §41.  The numerical fusion
alternative supplies the 21/45 orientation, the normalizer/type record
supplies the 40.3--40.5 local consequences, and the graph comparison carries
the actual source and model systems.  The final isomorphism is obtained by the
proved uniqueness-system recognition theorem, with the target pair-graph base
proved in `Graph`.
-/

@[expose] public section
namespace Theory.GroupTheory.TransvectionFive

open Subgroup

universe u v
variable {G : Type u} [Group G]
variable (hSimple : IsSimpleGroup G)
variable {z : G} (F : MarkedCentralizer z)

/-- The exact M24 implication once the measured source clauses and the actual
source/model graph comparison have been discharged. -/
public theorem mathieu_of_source_data
    (hSimple : IsSimpleGroup G)
    (_hcore : PointCoreFusion z)
    (witness : MathieuSourceWitness (G := G) F) :
    Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  let : IsSimpleGroup G := hSimple
  let : MulAction G witness.W := witness.action
  exact witness.graphData.exists_mulEquiv

/-- A convenient form using the original `MathieuFusion` predicate. -/
public theorem mathieu_of_mathieuFusion
    (hSimple : IsSimpleGroup G)
    (hcore : PointCoreFusion z)
    (hfusion : F.MathieuFusion)
    (witness : MathieuSourceWitness (G := G) F) :
    Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  have _horientation : MathieuFusionOrientation F ∨
      MathieuFusionOppositeOrientation F :=
    mathieuFusion_cases F hfusion
  exact mathieu_of_source_data F hSimple hcore witness

end Theory.GroupTheory.TransvectionFive
