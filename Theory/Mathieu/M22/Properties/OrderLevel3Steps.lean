module

public import Theory.Mathieu.M22.Properties.OrderLevel3Data

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000


private theorem m22L3Step_pointwise : (i : Fin 6) -> (r : Fin 16) ->
    m22L3Gen i * m22L3Rep r =
      m22L3Rep (m22L3Act i r) * evalWord m22L4Gen (m22L3Factor i r) := by
  decide +kernel

public theorem m22L3Step0 (r : Fin 16) :
    m22L3Gen 0 * m22L3Rep r =
      m22L3Rep (m22L3Act 0 r) * evalWord m22L4Gen (m22L3Factor 0 r):=
  m22L3Step_pointwise 0 r
public theorem m22L3Step1 (r : Fin 16) :
    m22L3Gen 1 * m22L3Rep r =
      m22L3Rep (m22L3Act 1 r) * evalWord m22L4Gen (m22L3Factor 1 r):=
  m22L3Step_pointwise 1 r
public theorem m22L3Step2 (r : Fin 16) :
    m22L3Gen 2 * m22L3Rep r =
      m22L3Rep (m22L3Act 2 r) * evalWord m22L4Gen (m22L3Factor 2 r):=
  m22L3Step_pointwise 2 r
public theorem m22L3Step3 (r : Fin 16) :
    m22L3Gen 3 * m22L3Rep r =
      m22L3Rep (m22L3Act 3 r) * evalWord m22L4Gen (m22L3Factor 3 r):=
  m22L3Step_pointwise 3 r
public theorem m22L3Step4 (r : Fin 16) :
    m22L3Gen 4 * m22L3Rep r =
      m22L3Rep (m22L3Act 4 r) * evalWord m22L4Gen (m22L3Factor 4 r):=
  m22L3Step_pointwise 4 r
public theorem m22L3Step5 (r : Fin 16) :
    m22L3Gen 5 * m22L3Rep r =
      m22L3Rep (m22L3Act 5 r) * evalWord m22L4Gen (m22L3Factor 5 r):=
  m22L3Step_pointwise 5 r

public theorem m22L3Step : (i : Fin 6) -> (r : Fin 16) ->
    m22L3Gen i * m22L3Rep r =
      m22L3Rep (m22L3Act i r) * evalWord m22L4Gen (m22L3Factor i r) :=
  m22L3Step_pointwise

end Sporadic.Mathieu
