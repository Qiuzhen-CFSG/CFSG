module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport2

/-!
# Lyons plane transport through wordB, step 4

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 4 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b22_valid : valid b21 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b22_check : check atlasBRows b21 b22 = true := by
  decide +kernel

private theorem b22_step :
    matrixRepresentation generatorB * decode b21 = decode b22 :=
  sound atlasBRows b21 b22 b22_valid b22_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b23_valid : valid b22 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b23_check : check atlasBRows b22 b23 = true := by
  decide +kernel

private theorem b23_step :
    matrixRepresentation generatorB * decode b22 = decode b23 :=
  sound atlasBRows b22 b23 b23_valid b23_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b24_valid : valid b23 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b24_check : check atlasARows b23 b24 = true := by
  decide +kernel

private theorem b24_step :
    matrixRepresentation generatorA * decode b23 = decode b24 :=
  sound atlasARows b23 b24 b24_valid b24_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b25_valid : valid b24 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b25_check : check atlasBRows b24 b25 = true := by
  decide +kernel

private theorem b25_step :
    matrixRepresentation generatorB * decode b24 = decode b25 :=
  sound atlasBRows b24 b25 b25_valid b25_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b26_valid : valid b25 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b26_check : check atlasARows b25 b26 = true := by
  decide +kernel

private theorem b26_step :
    matrixRepresentation generatorA * decode b25 = decode b26 :=
  sound atlasARows b25 b26 b26_valid b26_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b27_valid : valid b26 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b27_check : check atlasBRows b26 b27 = true := by
  decide +kernel

private theorem b27_step :
    matrixRepresentation generatorB * decode b26 = decode b27 :=
  sound atlasBRows b26 b27 b27_valid b27_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b28_valid : valid b27 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b28_check : check atlasARows b27 b28 = true := by
  decide +kernel

private theorem b28_step :
    matrixRepresentation generatorA * decode b27 = decode b28 :=
  sound atlasARows b27 b28 b28_valid b28_check

private theorem b_word3 :
    matrixRepresentation wordB * decode b21 = decode b28 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b22_step, b23_step, b24_step, b25_step, b26_step, b27_step, b28_step]

public theorem b_power4 :
    matrixRepresentation (wordB ^ 4) * decode b0 = decode b28 := by
  exact power_step wordB 3 _ _ _ b_power3 b_word3

end Lyons.OrderCertificate.PlaneTransport
