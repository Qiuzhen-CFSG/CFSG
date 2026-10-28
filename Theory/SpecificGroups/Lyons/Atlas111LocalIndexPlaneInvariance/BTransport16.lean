module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport15

/-!
# Lyons plane transport through wordB, step 17

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 17 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b113_valid : valid b112 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b113_check : check atlasBRows b112 b113 = true := by
  decide +kernel

private theorem b113_step :
    matrixRepresentation generatorB * decode b112 = decode b113 :=
  sound atlasBRows b112 b113 b113_valid b113_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b114_valid : valid b113 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b114_check : check atlasBRows b113 b114 = true := by
  decide +kernel

private theorem b114_step :
    matrixRepresentation generatorB * decode b113 = decode b114 :=
  sound atlasBRows b113 b114 b114_valid b114_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b115_valid : valid b114 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b115_check : check atlasARows b114 b115 = true := by
  decide +kernel

private theorem b115_step :
    matrixRepresentation generatorA * decode b114 = decode b115 :=
  sound atlasARows b114 b115 b115_valid b115_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b116_valid : valid b115 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b116_check : check atlasBRows b115 b116 = true := by
  decide +kernel

private theorem b116_step :
    matrixRepresentation generatorB * decode b115 = decode b116 :=
  sound atlasBRows b115 b116 b116_valid b116_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b117_valid : valid b116 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b117_check : check atlasARows b116 b117 = true := by
  decide +kernel

private theorem b117_step :
    matrixRepresentation generatorA * decode b116 = decode b117 :=
  sound atlasARows b116 b117 b117_valid b117_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b118_valid : valid b117 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b118_check : check atlasBRows b117 b118 = true := by
  decide +kernel

private theorem b118_step :
    matrixRepresentation generatorB * decode b117 = decode b118 :=
  sound atlasBRows b117 b118 b118_valid b118_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b119_valid : valid b118 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b119_check : check atlasARows b118 b119 = true := by
  decide +kernel

private theorem b119_step :
    matrixRepresentation generatorA * decode b118 = decode b119 :=
  sound atlasARows b118 b119 b119_valid b119_check

private theorem b_word16 :
    matrixRepresentation wordB * decode b112 = decode b119 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b113_step, b114_step, b115_step, b116_step, b117_step, b118_step, b119_step]

public theorem b_power17 :
    matrixRepresentation (wordB ^ 17) * decode b0 = decode b119 := by
  exact power_step wordB 16 _ _ _ b_power16 b_word16

end Lyons.OrderCertificate.PlaneTransport
