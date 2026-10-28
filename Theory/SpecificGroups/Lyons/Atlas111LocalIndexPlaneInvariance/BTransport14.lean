module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport13

/-!
# Lyons plane transport through wordB, step 15

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 15 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b99_valid : valid b98 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b99_check : check atlasBRows b98 b99 = true := by
  decide +kernel

private theorem b99_step :
    matrixRepresentation generatorB * decode b98 = decode b99 :=
  sound atlasBRows b98 b99 b99_valid b99_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b100_valid : valid b99 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b100_check : check atlasBRows b99 b100 = true := by
  decide +kernel

private theorem b100_step :
    matrixRepresentation generatorB * decode b99 = decode b100 :=
  sound atlasBRows b99 b100 b100_valid b100_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b101_valid : valid b100 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b101_check : check atlasARows b100 b101 = true := by
  decide +kernel

private theorem b101_step :
    matrixRepresentation generatorA * decode b100 = decode b101 :=
  sound atlasARows b100 b101 b101_valid b101_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b102_valid : valid b101 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b102_check : check atlasBRows b101 b102 = true := by
  decide +kernel

private theorem b102_step :
    matrixRepresentation generatorB * decode b101 = decode b102 :=
  sound atlasBRows b101 b102 b102_valid b102_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b103_valid : valid b102 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b103_check : check atlasARows b102 b103 = true := by
  decide +kernel

private theorem b103_step :
    matrixRepresentation generatorA * decode b102 = decode b103 :=
  sound atlasARows b102 b103 b103_valid b103_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b104_valid : valid b103 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b104_check : check atlasBRows b103 b104 = true := by
  decide +kernel

private theorem b104_step :
    matrixRepresentation generatorB * decode b103 = decode b104 :=
  sound atlasBRows b103 b104 b104_valid b104_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b105_valid : valid b104 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b105_check : check atlasARows b104 b105 = true := by
  decide +kernel

private theorem b105_step :
    matrixRepresentation generatorA * decode b104 = decode b105 :=
  sound atlasARows b104 b105 b105_valid b105_check

private theorem b_word14 :
    matrixRepresentation wordB * decode b98 = decode b105 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b99_step, b100_step, b101_step, b102_step, b103_step, b104_step, b105_step]

public theorem b_power15 :
    matrixRepresentation (wordB ^ 15) * decode b0 = decode b105 := by
  exact power_step wordB 14 _ _ _ b_power14 b_word14

end Lyons.OrderCertificate.PlaneTransport
