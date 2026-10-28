module

public import Theory.Mathieu.M11.Properties.Order
public import Theory.GroupTheory.SharpTransitivity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

/-- The natural degree-11 action of M11 is sharply four-transitive. -/
public theorem m11_isSharplyFourPretransitive :
    Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive M11 (Fin 11) 4 :=
  Theory.GroupTheory.MulAction.isSharplyMultiplyPretransitive_of_bijective_orbitMap
    m11FourPointBase m11_fourPointOrbitMap_bijective

/-- The natural degree-11 action of M11 is four-transitive. -/
public theorem m11_isFourPretransitive :
    MulAction.IsMultiplyPretransitive M11 (Fin 11) 4 :=
  m11_isSharplyFourPretransitive.isMultiplyPretransitive

end Sporadic.Mathieu
