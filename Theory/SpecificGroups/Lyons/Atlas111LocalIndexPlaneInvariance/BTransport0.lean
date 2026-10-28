module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.Data
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.Words

/-!
# Lyons plane transport through wordB, step 1

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 1 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b1_valid : valid b0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b1_check : check atlasBRows b0 b1 = true := by
  decide +kernel

private theorem b1_step :
    matrixRepresentation generatorB * decode b0 = decode b1 :=
  sound atlasBRows b0 b1 b1_valid b1_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b2_valid : valid b1 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b2_check : check atlasBRows b1 b2 = true := by
  decide +kernel

private theorem b2_step :
    matrixRepresentation generatorB * decode b1 = decode b2 :=
  sound atlasBRows b1 b2 b2_valid b2_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b3_valid : valid b2 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b3_check : check atlasARows b2 b3 = true := by
  decide +kernel

private theorem b3_step :
    matrixRepresentation generatorA * decode b2 = decode b3 :=
  sound atlasARows b2 b3 b3_valid b3_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b4_valid : valid b3 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b4_check : check atlasBRows b3 b4 = true := by
  decide +kernel

private theorem b4_step :
    matrixRepresentation generatorB * decode b3 = decode b4 :=
  sound atlasBRows b3 b4 b4_valid b4_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b5_valid : valid b4 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b5_check : check atlasARows b4 b5 = true := by
  decide +kernel

private theorem b5_step :
    matrixRepresentation generatorA * decode b4 = decode b5 :=
  sound atlasARows b4 b5 b5_valid b5_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b6_valid : valid b5 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b6_check : check atlasBRows b5 b6 = true := by
  decide +kernel

private theorem b6_step :
    matrixRepresentation generatorB * decode b5 = decode b6 :=
  sound atlasBRows b5 b6 b6_valid b6_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b7_valid : valid b6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b7_check : check atlasARows b6 b7 = true := by
  decide +kernel

private theorem b7_step :
    matrixRepresentation generatorA * decode b6 = decode b7 :=
  sound atlasARows b6 b7 b7_valid b7_check

private theorem b_word0 :
    matrixRepresentation wordB * decode b0 = decode b7 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b1_step, b2_step, b3_step, b4_step, b5_step, b6_step, b7_step]

public theorem b_power1 :
    matrixRepresentation (wordB ^ 1) * decode b0 = decode b7 := by
  simpa only [pow_one] using b_word0

end Lyons.OrderCertificate.PlaneTransport
