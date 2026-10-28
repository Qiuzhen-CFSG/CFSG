module

public import Theory.Mathieu.M22.Properties.OrderLevel1Data

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000


private theorem m22L1Step_pointwise : (i : Fin 6) -> (r : Fin 21) ->
    m22L1Gen i * m22L1Rep r =
      m22L1Rep (m22L1Act i r) * evalWord m22L2Gen (m22L1Factor i r) := by
  decide +kernel

public theorem m22L1Step0 (r : Fin 21) :
    m22L1Gen (0 : Fin 6) * m22L1Rep r =
      m22L1Rep (m22L1Act (0 : Fin 6) r) *
        evalWord m22L2Gen (m22L1Factor (0 : Fin 6) r) :=
  m22L1Step_pointwise 0 r

public theorem m22L1Step1 (r : Fin 21) :
    m22L1Gen (1 : Fin 6) * m22L1Rep r =
      m22L1Rep (m22L1Act (1 : Fin 6) r) *
        evalWord m22L2Gen (m22L1Factor (1 : Fin 6) r) :=
  m22L1Step_pointwise 1 r

public theorem m22L1Step2 (r : Fin 21) :
    m22L1Gen (2 : Fin 6) * m22L1Rep r =
      m22L1Rep (m22L1Act (2 : Fin 6) r) *
        evalWord m22L2Gen (m22L1Factor (2 : Fin 6) r) :=
  m22L1Step_pointwise 2 r

public theorem m22L1Step3 (r : Fin 21) :
    m22L1Gen (3 : Fin 6) * m22L1Rep r =
      m22L1Rep (m22L1Act (3 : Fin 6) r) *
        evalWord m22L2Gen (m22L1Factor (3 : Fin 6) r) :=
  m22L1Step_pointwise 3 r

public theorem m22L1Step4 (r : Fin 21) :
    m22L1Gen (4 : Fin 6) * m22L1Rep r =
      m22L1Rep (m22L1Act (4 : Fin 6) r) *
        evalWord m22L2Gen (m22L1Factor (4 : Fin 6) r) :=
  m22L1Step_pointwise 4 r

public theorem m22L1Step5 (r : Fin 21) :
    m22L1Gen (5 : Fin 6) * m22L1Rep r =
      m22L1Rep (m22L1Act (5 : Fin 6) r) *
        evalWord m22L2Gen (m22L1Factor (5 : Fin 6) r) :=
  m22L1Step_pointwise 5 r

public theorem m22L1Step : (i : Fin 6) -> (r : Fin 21) ->
    m22L1Gen i * m22L1Rep r =
      m22L1Rep (m22L1Act i r) * evalWord m22L2Gen (m22L1Factor i r) :=
  m22L1Step_pointwise

end Sporadic.Mathieu
