module

public import Theory.Mathieu.M22.Properties.Transitivity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

/-- The point-1 stabilizer, the standard L3(4) maximal subgroup, is maximal in M22. -/
public theorem m22PointStabilizerOne_isCoatom :
    IsCoatom (MulAction.stabilizer M22 (1 : Fin 22)) := by
  let : MulAction.IsPreprimitive M22 (Fin 22) := m22_isPreprimitive
  exact
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      M22 (1 : Fin 22)

end Sporadic.Mathieu
