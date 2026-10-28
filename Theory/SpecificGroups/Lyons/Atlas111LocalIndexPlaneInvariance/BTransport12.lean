module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport11

/-!
# Lyons plane transport through wordB, step 13

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 13 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b85_valid : valid b84 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b85_check : check atlasBRows b84 b85 = true := by
  decide +kernel

private theorem b85_step :
    matrixRepresentation generatorB * decode b84 = decode b85 :=
  sound atlasBRows b84 b85 b85_valid b85_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b86_valid : valid b85 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b86_check : check atlasBRows b85 b86 = true := by
  decide +kernel

private theorem b86_step :
    matrixRepresentation generatorB * decode b85 = decode b86 :=
  sound atlasBRows b85 b86 b86_valid b86_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b87_valid : valid b86 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b87_check : check atlasARows b86 b87 = true := by
  decide +kernel

private theorem b87_step :
    matrixRepresentation generatorA * decode b86 = decode b87 :=
  sound atlasARows b86 b87 b87_valid b87_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b88_valid : valid b87 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b88_check : check atlasBRows b87 b88 = true := by
  decide +kernel

private theorem b88_step :
    matrixRepresentation generatorB * decode b87 = decode b88 :=
  sound atlasBRows b87 b88 b88_valid b88_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b89_valid : valid b88 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b89_check : check atlasARows b88 b89 = true := by
  decide +kernel

private theorem b89_step :
    matrixRepresentation generatorA * decode b88 = decode b89 :=
  sound atlasARows b88 b89 b89_valid b89_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b90_valid : valid b89 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b90_check : check atlasBRows b89 b90 = true := by
  decide +kernel

private theorem b90_step :
    matrixRepresentation generatorB * decode b89 = decode b90 :=
  sound atlasBRows b89 b90 b90_valid b90_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b91_valid : valid b90 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b91_check : check atlasARows b90 b91 = true := by
  decide +kernel

private theorem b91_step :
    matrixRepresentation generatorA * decode b90 = decode b91 :=
  sound atlasARows b90 b91 b91_valid b91_check

private theorem b_word12 :
    matrixRepresentation wordB * decode b84 = decode b91 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b85_step, b86_step, b87_step, b88_step, b89_step, b90_step, b91_step]

public theorem b_power13 :
    matrixRepresentation (wordB ^ 13) * decode b0 = decode b91 := by
  exact power_step wordB 12 _ _ _ b_power12 b_word12

end Lyons.OrderCertificate.PlaneTransport
