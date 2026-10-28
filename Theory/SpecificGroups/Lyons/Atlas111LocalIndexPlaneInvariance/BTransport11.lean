module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport10

/-!
# Lyons plane transport through wordB, step 12

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 12 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b78_valid : valid b77 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b78_check : check atlasBRows b77 b78 = true := by
  decide +kernel

private theorem b78_step :
    matrixRepresentation generatorB * decode b77 = decode b78 :=
  sound atlasBRows b77 b78 b78_valid b78_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b79_valid : valid b78 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b79_check : check atlasBRows b78 b79 = true := by
  decide +kernel

private theorem b79_step :
    matrixRepresentation generatorB * decode b78 = decode b79 :=
  sound atlasBRows b78 b79 b79_valid b79_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b80_valid : valid b79 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b80_check : check atlasARows b79 b80 = true := by
  decide +kernel

private theorem b80_step :
    matrixRepresentation generatorA * decode b79 = decode b80 :=
  sound atlasARows b79 b80 b80_valid b80_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b81_valid : valid b80 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b81_check : check atlasBRows b80 b81 = true := by
  decide +kernel

private theorem b81_step :
    matrixRepresentation generatorB * decode b80 = decode b81 :=
  sound atlasBRows b80 b81 b81_valid b81_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b82_valid : valid b81 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b82_check : check atlasARows b81 b82 = true := by
  decide +kernel

private theorem b82_step :
    matrixRepresentation generatorA * decode b81 = decode b82 :=
  sound atlasARows b81 b82 b82_valid b82_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b83_valid : valid b82 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b83_check : check atlasBRows b82 b83 = true := by
  decide +kernel

private theorem b83_step :
    matrixRepresentation generatorB * decode b82 = decode b83 :=
  sound atlasBRows b82 b83 b83_valid b83_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b84_valid : valid b83 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b84_check : check atlasARows b83 b84 = true := by
  decide +kernel

private theorem b84_step :
    matrixRepresentation generatorA * decode b83 = decode b84 :=
  sound atlasARows b83 b84 b84_valid b84_check

private theorem b_word11 :
    matrixRepresentation wordB * decode b77 = decode b84 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b78_step, b79_step, b80_step, b81_step, b82_step, b83_step, b84_step]

public theorem b_power12 :
    matrixRepresentation (wordB ^ 12) * decode b0 = decode b84 := by
  exact power_step wordB 11 _ _ _ b_power11 b_word11

end Lyons.OrderCertificate.PlaneTransport
