module

public import Theory.Mathieu.M23.Properties.Transitivity
public import Theory.Mathieu.M23.Properties.Simplicity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

/-- The point-9 stabilizer, identified with M22, is maximal in M23. -/
public theorem m23PointStabilizerNine_isCoatom :
    IsCoatom (MulAction.stabilizer M23 (9 : Fin 23)) := by
  let : MulAction.IsPreprimitive M23 (Fin 23) := m23_isPreprimitive
  exact
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      M23 (9 : Fin 23)

end Sporadic.Mathieu
