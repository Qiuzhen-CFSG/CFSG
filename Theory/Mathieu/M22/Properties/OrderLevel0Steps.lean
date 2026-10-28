module

public import Theory.Mathieu.M22.Properties.OrderLevel0Data

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000


private theorem m22L0Step_pointwise : (i : Fin 4) -> (r : Fin 22) ->
    m22L0Gen i * m22L0Rep r =
      m22L0Rep (m22L0Act i r) * evalWord m22L1Gen (m22L0Factor i r) := by
  decide +kernel

public theorem m22L0Step0 (r : Fin 22) :
    m22L0Gen (0 : Fin 4) * m22L0Rep r =
      m22L0Rep (m22L0Act (0 : Fin 4) r) *
        evalWord m22L1Gen (m22L0Factor (0 : Fin 4) r) :=
  m22L0Step_pointwise 0 r

public theorem m22L0Step1 (r : Fin 22) :
    m22L0Gen (1 : Fin 4) * m22L0Rep r =
      m22L0Rep (m22L0Act (1 : Fin 4) r) *
        evalWord m22L1Gen (m22L0Factor (1 : Fin 4) r) :=
  m22L0Step_pointwise 1 r

public theorem m22L0Step2 (r : Fin 22) :
    m22L0Gen (2 : Fin 4) * m22L0Rep r =
      m22L0Rep (m22L0Act (2 : Fin 4) r) *
        evalWord m22L1Gen (m22L0Factor (2 : Fin 4) r) :=
  m22L0Step_pointwise 2 r

public theorem m22L0Step3 (r : Fin 22) :
    m22L0Gen (3 : Fin 4) * m22L0Rep r =
      m22L0Rep (m22L0Act (3 : Fin 4) r) *
        evalWord m22L1Gen (m22L0Factor (3 : Fin 4) r) :=
  m22L0Step_pointwise 3 r

public theorem m22L0Step : (i : Fin 4) -> (r : Fin 22) ->
    m22L0Gen i * m22L0Rep r =
      m22L0Rep (m22L0Act i r) * evalWord m22L1Gen (m22L0Factor i r) :=
  m22L0Step_pointwise

end Sporadic.Mathieu
