module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport1

/-!
# Lyons plane transport through wordB, step 3

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 3 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b15_valid : valid b14 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b15_check : check atlasBRows b14 b15 = true := by
  decide +kernel

private theorem b15_step :
    matrixRepresentation generatorB * decode b14 = decode b15 :=
  sound atlasBRows b14 b15 b15_valid b15_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b16_valid : valid b15 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b16_check : check atlasBRows b15 b16 = true := by
  decide +kernel

private theorem b16_step :
    matrixRepresentation generatorB * decode b15 = decode b16 :=
  sound atlasBRows b15 b16 b16_valid b16_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b17_valid : valid b16 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b17_check : check atlasARows b16 b17 = true := by
  decide +kernel

private theorem b17_step :
    matrixRepresentation generatorA * decode b16 = decode b17 :=
  sound atlasARows b16 b17 b17_valid b17_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b18_valid : valid b17 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b18_check : check atlasBRows b17 b18 = true := by
  decide +kernel

private theorem b18_step :
    matrixRepresentation generatorB * decode b17 = decode b18 :=
  sound atlasBRows b17 b18 b18_valid b18_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b19_valid : valid b18 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b19_check : check atlasARows b18 b19 = true := by
  decide +kernel

private theorem b19_step :
    matrixRepresentation generatorA * decode b18 = decode b19 :=
  sound atlasARows b18 b19 b19_valid b19_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b20_valid : valid b19 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b20_check : check atlasBRows b19 b20 = true := by
  decide +kernel

private theorem b20_step :
    matrixRepresentation generatorB * decode b19 = decode b20 :=
  sound atlasBRows b19 b20 b20_valid b20_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b21_valid : valid b20 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b21_check : check atlasARows b20 b21 = true := by
  decide +kernel

private theorem b21_step :
    matrixRepresentation generatorA * decode b20 = decode b21 :=
  sound atlasARows b20 b21 b21_valid b21_check

private theorem b_word2 :
    matrixRepresentation wordB * decode b14 = decode b21 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b15_step, b16_step, b17_step, b18_step, b19_step, b20_step, b21_step]

public theorem b_power3 :
    matrixRepresentation (wordB ^ 3) * decode b0 = decode b21 := by
  exact power_step wordB 2 _ _ _ b_power2 b_word2

end Lyons.OrderCertificate.PlaneTransport
