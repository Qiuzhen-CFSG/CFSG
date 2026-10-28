module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport0

/-!
# Lyons plane transport through wordB, step 2

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 2 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b8_valid : valid b7 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b8_check : check atlasBRows b7 b8 = true := by
  decide +kernel

private theorem b8_step :
    matrixRepresentation generatorB * decode b7 = decode b8 :=
  sound atlasBRows b7 b8 b8_valid b8_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b9_valid : valid b8 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b9_check : check atlasBRows b8 b9 = true := by
  decide +kernel

private theorem b9_step :
    matrixRepresentation generatorB * decode b8 = decode b9 :=
  sound atlasBRows b8 b9 b9_valid b9_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b10_valid : valid b9 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b10_check : check atlasARows b9 b10 = true := by
  decide +kernel

private theorem b10_step :
    matrixRepresentation generatorA * decode b9 = decode b10 :=
  sound atlasARows b9 b10 b10_valid b10_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b11_valid : valid b10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b11_check : check atlasBRows b10 b11 = true := by
  decide +kernel

private theorem b11_step :
    matrixRepresentation generatorB * decode b10 = decode b11 :=
  sound atlasBRows b10 b11 b11_valid b11_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b12_valid : valid b11 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b12_check : check atlasARows b11 b12 = true := by
  decide +kernel

private theorem b12_step :
    matrixRepresentation generatorA * decode b11 = decode b12 :=
  sound atlasARows b11 b12 b12_valid b12_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b13_valid : valid b12 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b13_check : check atlasBRows b12 b13 = true := by
  decide +kernel

private theorem b13_step :
    matrixRepresentation generatorB * decode b12 = decode b13 :=
  sound atlasBRows b12 b13 b13_valid b13_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b14_valid : valid b13 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b14_check : check atlasARows b13 b14 = true := by
  decide +kernel

private theorem b14_step :
    matrixRepresentation generatorA * decode b13 = decode b14 :=
  sound atlasARows b13 b14 b14_valid b14_check

private theorem b_word1 :
    matrixRepresentation wordB * decode b7 = decode b14 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b8_step, b9_step, b10_step, b11_step, b12_step, b13_step, b14_step]

public theorem b_power2 :
    matrixRepresentation (wordB ^ 2) * decode b0 = decode b14 := by
  exact power_step wordB 1 _ _ _ b_power1 b_word1

end Lyons.OrderCertificate.PlaneTransport
