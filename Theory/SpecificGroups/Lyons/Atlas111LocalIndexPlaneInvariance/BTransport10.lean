module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport9

/-!
# Lyons plane transport through wordB, step 11

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 11 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b71_valid : valid b70 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b71_check : check atlasBRows b70 b71 = true := by
  decide +kernel

private theorem b71_step :
    matrixRepresentation generatorB * decode b70 = decode b71 :=
  sound atlasBRows b70 b71 b71_valid b71_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b72_valid : valid b71 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b72_check : check atlasBRows b71 b72 = true := by
  decide +kernel

private theorem b72_step :
    matrixRepresentation generatorB * decode b71 = decode b72 :=
  sound atlasBRows b71 b72 b72_valid b72_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b73_valid : valid b72 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b73_check : check atlasARows b72 b73 = true := by
  decide +kernel

private theorem b73_step :
    matrixRepresentation generatorA * decode b72 = decode b73 :=
  sound atlasARows b72 b73 b73_valid b73_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b74_valid : valid b73 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b74_check : check atlasBRows b73 b74 = true := by
  decide +kernel

private theorem b74_step :
    matrixRepresentation generatorB * decode b73 = decode b74 :=
  sound atlasBRows b73 b74 b74_valid b74_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b75_valid : valid b74 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b75_check : check atlasARows b74 b75 = true := by
  decide +kernel

private theorem b75_step :
    matrixRepresentation generatorA * decode b74 = decode b75 :=
  sound atlasARows b74 b75 b75_valid b75_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b76_valid : valid b75 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b76_check : check atlasBRows b75 b76 = true := by
  decide +kernel

private theorem b76_step :
    matrixRepresentation generatorB * decode b75 = decode b76 :=
  sound atlasBRows b75 b76 b76_valid b76_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b77_valid : valid b76 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b77_check : check atlasARows b76 b77 = true := by
  decide +kernel

private theorem b77_step :
    matrixRepresentation generatorA * decode b76 = decode b77 :=
  sound atlasARows b76 b77 b77_valid b77_check

private theorem b_word10 :
    matrixRepresentation wordB * decode b70 = decode b77 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b71_step, b72_step, b73_step, b74_step, b75_step, b76_step, b77_step]

public theorem b_power11 :
    matrixRepresentation (wordB ^ 11) * decode b0 = decode b77 := by
  exact power_step wordB 10 _ _ _ b_power10 b_word10

end Lyons.OrderCertificate.PlaneTransport
