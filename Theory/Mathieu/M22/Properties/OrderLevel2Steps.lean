module

public import Theory.Mathieu.M22.Properties.OrderLevel2Data

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000


private theorem m22L2Step_pointwise : (i : Fin 8) -> (r : Fin 20) ->
    m22L2Gen i * m22L2Rep r =
      m22L2Rep (m22L2Act i r) * evalWord m22L3Gen (m22L2Factor i r) := by
  decide +kernel

public theorem m22L2Step0 (r : Fin 20) :
    m22L2Gen 0 * m22L2Rep r =
      m22L2Rep (m22L2Act 0 r) * evalWord m22L3Gen (m22L2Factor 0 r) :=
  m22L2Step_pointwise 0 r
public theorem m22L2Step1 (r : Fin 20) :
    m22L2Gen 1 * m22L2Rep r =
      m22L2Rep (m22L2Act 1 r) * evalWord m22L3Gen (m22L2Factor 1 r) :=
  m22L2Step_pointwise 1 r
public theorem m22L2Step2 (r : Fin 20) :
    m22L2Gen 2 * m22L2Rep r =
      m22L2Rep (m22L2Act 2 r) * evalWord m22L3Gen (m22L2Factor 2 r) :=
  m22L2Step_pointwise 2 r
public theorem m22L2Step3 (r : Fin 20) :
    m22L2Gen 3 * m22L2Rep r =
      m22L2Rep (m22L2Act 3 r) * evalWord m22L3Gen (m22L2Factor 3 r) :=
  m22L2Step_pointwise 3 r
public theorem m22L2Step4 (r : Fin 20) :
    m22L2Gen 4 * m22L2Rep r =
      m22L2Rep (m22L2Act 4 r) * evalWord m22L3Gen (m22L2Factor 4 r) :=
  m22L2Step_pointwise 4 r
public theorem m22L2Step5 (r : Fin 20) :
    m22L2Gen 5 * m22L2Rep r =
      m22L2Rep (m22L2Act 5 r) * evalWord m22L3Gen (m22L2Factor 5 r) :=
  m22L2Step_pointwise 5 r
public theorem m22L2Step6 (r : Fin 20) :
    m22L2Gen 6 * m22L2Rep r =
      m22L2Rep (m22L2Act 6 r) * evalWord m22L3Gen (m22L2Factor 6 r) :=
  m22L2Step_pointwise 6 r
public theorem m22L2Step7 (r : Fin 20) :
    m22L2Gen 7 * m22L2Rep r =
      m22L2Rep (m22L2Act 7 r) * evalWord m22L3Gen (m22L2Factor 7 r) :=
  m22L2Step_pointwise 7 r

public theorem m22L2Step : (i : Fin 8) -> (r : Fin 20) ->
    m22L2Gen i * m22L2Rep r =
      m22L2Rep (m22L2Act i r) * evalWord m22L3Gen (m22L2Factor i r) :=
  m22L2Step_pointwise

end Sporadic.Mathieu
