module

public import Theory.Mathieu.M24.Properties.Transitivity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

/-- The point-24 stabilizer, identified with M23, is maximal in M24. -/
public theorem m24PointStabilizerTwentyFour_isCoatom :
    IsCoatom (MulAction.stabilizer M24 (24 : Fin 24)) := by
  let : MulAction.IsMultiplyPretransitive M24 (Fin 24) 5 :=
    m24_isFivePretransitive
  have htwo : MulAction.IsMultiplyPretransitive M24 (Fin 24) 2 :=
    MulAction.isMultiplyPretransitive_of_le
      (G := M24) (α := Fin 24) (m := 2) (n := 5) (by norm_num) (by norm_num)
  let : MulAction.IsPreprimitive M24 (Fin 24) :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  exact
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      M24 (24 : Fin 24)

end Sporadic.Mathieu
