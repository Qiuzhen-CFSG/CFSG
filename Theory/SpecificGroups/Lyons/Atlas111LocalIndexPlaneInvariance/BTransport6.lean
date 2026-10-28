module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport5

/-!
# Lyons plane transport through wordB, step 7

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 7 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b43_valid : valid b42 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b43_check : check atlasBRows b42 b43 = true := by
  decide +kernel

private theorem b43_step :
    matrixRepresentation generatorB * decode b42 = decode b43 :=
  sound atlasBRows b42 b43 b43_valid b43_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b44_valid : valid b43 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b44_check : check atlasBRows b43 b44 = true := by
  decide +kernel

private theorem b44_step :
    matrixRepresentation generatorB * decode b43 = decode b44 :=
  sound atlasBRows b43 b44 b44_valid b44_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b45_valid : valid b44 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b45_check : check atlasARows b44 b45 = true := by
  decide +kernel

private theorem b45_step :
    matrixRepresentation generatorA * decode b44 = decode b45 :=
  sound atlasARows b44 b45 b45_valid b45_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b46_valid : valid b45 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b46_check : check atlasBRows b45 b46 = true := by
  decide +kernel

private theorem b46_step :
    matrixRepresentation generatorB * decode b45 = decode b46 :=
  sound atlasBRows b45 b46 b46_valid b46_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b47_valid : valid b46 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b47_check : check atlasARows b46 b47 = true := by
  decide +kernel

private theorem b47_step :
    matrixRepresentation generatorA * decode b46 = decode b47 :=
  sound atlasARows b46 b47 b47_valid b47_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b48_valid : valid b47 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b48_check : check atlasBRows b47 b48 = true := by
  decide +kernel

private theorem b48_step :
    matrixRepresentation generatorB * decode b47 = decode b48 :=
  sound atlasBRows b47 b48 b48_valid b48_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b49_valid : valid b48 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b49_check : check atlasARows b48 b49 = true := by
  decide +kernel

private theorem b49_step :
    matrixRepresentation generatorA * decode b48 = decode b49 :=
  sound atlasARows b48 b49 b49_valid b49_check

private theorem b_word6 :
    matrixRepresentation wordB * decode b42 = decode b49 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b43_step, b44_step, b45_step, b46_step, b47_step, b48_step, b49_step]

public theorem b_power7 :
    matrixRepresentation (wordB ^ 7) * decode b0 = decode b49 := by
  exact power_step wordB 6 _ _ _ b_power6 b_word6

end Lyons.OrderCertificate.PlaneTransport
