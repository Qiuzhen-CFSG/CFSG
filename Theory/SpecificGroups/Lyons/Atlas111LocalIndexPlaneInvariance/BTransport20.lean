module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport19

/-!
# Lyons plane transport through wordB, step 21

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 21 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b141_valid : valid b140 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b141_check : check atlasBRows b140 b141 = true := by
  decide +kernel

private theorem b141_step :
    matrixRepresentation generatorB * decode b140 = decode b141 :=
  sound atlasBRows b140 b141 b141_valid b141_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b142_valid : valid b141 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b142_check : check atlasBRows b141 b142 = true := by
  decide +kernel

private theorem b142_step :
    matrixRepresentation generatorB * decode b141 = decode b142 :=
  sound atlasBRows b141 b142 b142_valid b142_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b143_valid : valid b142 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b143_check : check atlasARows b142 b143 = true := by
  decide +kernel

private theorem b143_step :
    matrixRepresentation generatorA * decode b142 = decode b143 :=
  sound atlasARows b142 b143 b143_valid b143_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b144_valid : valid b143 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b144_check : check atlasBRows b143 b144 = true := by
  decide +kernel

private theorem b144_step :
    matrixRepresentation generatorB * decode b143 = decode b144 :=
  sound atlasBRows b143 b144 b144_valid b144_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b145_valid : valid b144 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b145_check : check atlasARows b144 b145 = true := by
  decide +kernel

private theorem b145_step :
    matrixRepresentation generatorA * decode b144 = decode b145 :=
  sound atlasARows b144 b145 b145_valid b145_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b146_valid : valid b145 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b146_check : check atlasBRows b145 b146 = true := by
  decide +kernel

private theorem b146_step :
    matrixRepresentation generatorB * decode b145 = decode b146 :=
  sound atlasBRows b145 b146 b146_valid b146_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b147_valid : valid b146 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b147_check : check atlasARows b146 b147 = true := by
  decide +kernel

private theorem b147_step :
    matrixRepresentation generatorA * decode b146 = decode b147 :=
  sound atlasARows b146 b147 b147_valid b147_check

private theorem b_word20 :
    matrixRepresentation wordB * decode b140 = decode b147 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b141_step, b142_step, b143_step, b144_step, b145_step, b146_step, b147_step]

public theorem b_power21 :
    matrixRepresentation (wordB ^ 21) * decode b0 = decode b147 := by
  exact power_step wordB 20 _ _ _ b_power20 b_word20

end Lyons.OrderCertificate.PlaneTransport
