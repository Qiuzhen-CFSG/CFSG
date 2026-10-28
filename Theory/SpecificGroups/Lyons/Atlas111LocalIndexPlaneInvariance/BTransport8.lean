module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport7

/-!
# Lyons plane transport through wordB, step 9

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 9 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b57_valid : valid b56 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b57_check : check atlasBRows b56 b57 = true := by
  decide +kernel

private theorem b57_step :
    matrixRepresentation generatorB * decode b56 = decode b57 :=
  sound atlasBRows b56 b57 b57_valid b57_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b58_valid : valid b57 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b58_check : check atlasBRows b57 b58 = true := by
  decide +kernel

private theorem b58_step :
    matrixRepresentation generatorB * decode b57 = decode b58 :=
  sound atlasBRows b57 b58 b58_valid b58_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b59_valid : valid b58 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b59_check : check atlasARows b58 b59 = true := by
  decide +kernel

private theorem b59_step :
    matrixRepresentation generatorA * decode b58 = decode b59 :=
  sound atlasARows b58 b59 b59_valid b59_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b60_valid : valid b59 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b60_check : check atlasBRows b59 b60 = true := by
  decide +kernel

private theorem b60_step :
    matrixRepresentation generatorB * decode b59 = decode b60 :=
  sound atlasBRows b59 b60 b60_valid b60_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b61_valid : valid b60 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b61_check : check atlasARows b60 b61 = true := by
  decide +kernel

private theorem b61_step :
    matrixRepresentation generatorA * decode b60 = decode b61 :=
  sound atlasARows b60 b61 b61_valid b61_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b62_valid : valid b61 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b62_check : check atlasBRows b61 b62 = true := by
  decide +kernel

private theorem b62_step :
    matrixRepresentation generatorB * decode b61 = decode b62 :=
  sound atlasBRows b61 b62 b62_valid b62_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b63_valid : valid b62 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b63_check : check atlasARows b62 b63 = true := by
  decide +kernel

private theorem b63_step :
    matrixRepresentation generatorA * decode b62 = decode b63 :=
  sound atlasARows b62 b63 b63_valid b63_check

private theorem b_word8 :
    matrixRepresentation wordB * decode b56 = decode b63 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b57_step, b58_step, b59_step, b60_step, b61_step, b62_step, b63_step]

public theorem b_power9 :
    matrixRepresentation (wordB ^ 9) * decode b0 = decode b63 := by
  exact power_step wordB 8 _ _ _ b_power8 b_word8

end Lyons.OrderCertificate.PlaneTransport
