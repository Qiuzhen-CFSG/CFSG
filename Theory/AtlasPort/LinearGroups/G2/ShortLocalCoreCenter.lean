module
public import Theory.GroupTheory.PCoreCenterEmbedding
public import Theory.AtlasPort.LinearGroups.G2.LieCoreSpecialness

/-!
# The short G₂ local factor centralizes its core center

The five-root radical and the full positive unipotent group have the same
highest-root center. The short local factor centralizes that root group.
Transport through the literal two-core identification gives the intrinsic
centrality used in the point-component inspection.

Source: Aschbacher--Smith F.1.12(I)(3), pp.262--264, and 10.2.9,
pp.750--751. The existing ATLAS root calculations retain their attribution.
-/

public section
open Subgroup
namespace Atlas.G2.LieParabolicSetup
/-- The first local factor centralizes the center of its own two-core. -/
theorem local₁_core_center_le_center
    {F : Type*} [Field F] [Finite F] [CharP F 2] :
    let B := Atlas.G2.LieParabolicSetup.local₁ (F := F)
    (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  open Atlas.G2.LieParabolicSetup in
  apply center_pCore_map_le_center_of_embedded local₁ radical₁ local₁_pCoreIn
  open Atlas.G2.LieParabolicSetup in
  rw [center_map_eq_highestRoot radical₁ le_rfl (fiveRootSubgroup_le_unipotent _ _)]
  open Atlas.G2.LieParabolicSetup in
  rintro z ⟨a,rfl⟩ l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA a.toAdd hl)

end Atlas.G2.LieParabolicSetup
