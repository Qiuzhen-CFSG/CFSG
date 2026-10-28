module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.ATransport6
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.CTransport2

/-!
# The concrete seven-dimensional Lyons plane is locally invariant

The kernel-checked transport chains follow the expanded literal ATLAS subgroup
program. The first chain transports a conjugate plane through the seventh power
of `ABAB³`; the second transports the displayed plane through the twenty-fifth
power of `ABABAB²`, then through the cube of `ABABAB²AB`. The small action
identities at the endpoints and cancellation of the conjugating words give the
two requested intertwining identities in the original matrix representation.

All numerical certificates are checked by kernel reduction. Their arithmetic
soundness is proved in `Atlas111LocalIndexPlaneInvariance.Arithmetic`.
Source matrices, subgroup program, and candidate generation are recorded in
`Atlas111Source/`, `Atlas111OrderSource/`, and `Atlas111SeparationSource/`.
-/

namespace Lyons.OrderCertificate
open PlaneTransport

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem decode_planeRows : decode planeRows = separationPlaneColumns := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a_initial_action :
    matrixRepresentation generatorA * decode a0 = decode aAction :=
  sound atlasARows a0 aAction (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a_small_action :
    decode aAction = decode a0 * separationPlaneActionA := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b_small_action :
    decode c27 = decode b175 * separationPlaneActionB := by
  decide +kernel

/-- The first literal local generator induces the displayed seven-dimensional action. -/
public theorem separationPlaneColumns_localA :
    matrixRepresentation localA * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionA :=
  localA_of_transport (decode a0) (a_power7.trans decode_planeRows)
    (a_initial_action.trans a_small_action)

/-- The second literal local generator induces the displayed seven-dimensional action. -/
public theorem separationPlaneColumns_localB :
    matrixRepresentation localB * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionB := by
  apply localB_of_transport (decode b175)
  · rw [← decode_planeRows]
    exact b_power25
  · exact c_power3.trans b_small_action

end Lyons.OrderCertificate
