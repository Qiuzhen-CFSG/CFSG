module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport3

/-!
# Lyons plane transport through wordB, step 5

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 5 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b29_valid : valid b28 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b29_check : check atlasBRows b28 b29 = true := by
  decide +kernel

private theorem b29_step :
    matrixRepresentation generatorB * decode b28 = decode b29 :=
  sound atlasBRows b28 b29 b29_valid b29_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b30_valid : valid b29 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b30_check : check atlasBRows b29 b30 = true := by
  decide +kernel

private theorem b30_step :
    matrixRepresentation generatorB * decode b29 = decode b30 :=
  sound atlasBRows b29 b30 b30_valid b30_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b31_valid : valid b30 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b31_check : check atlasARows b30 b31 = true := by
  decide +kernel

private theorem b31_step :
    matrixRepresentation generatorA * decode b30 = decode b31 :=
  sound atlasARows b30 b31 b31_valid b31_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b32_valid : valid b31 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b32_check : check atlasBRows b31 b32 = true := by
  decide +kernel

private theorem b32_step :
    matrixRepresentation generatorB * decode b31 = decode b32 :=
  sound atlasBRows b31 b32 b32_valid b32_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b33_valid : valid b32 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b33_check : check atlasARows b32 b33 = true := by
  decide +kernel

private theorem b33_step :
    matrixRepresentation generatorA * decode b32 = decode b33 :=
  sound atlasARows b32 b33 b33_valid b33_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b34_valid : valid b33 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b34_check : check atlasBRows b33 b34 = true := by
  decide +kernel

private theorem b34_step :
    matrixRepresentation generatorB * decode b33 = decode b34 :=
  sound atlasBRows b33 b34 b34_valid b34_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b35_valid : valid b34 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b35_check : check atlasARows b34 b35 = true := by
  decide +kernel

private theorem b35_step :
    matrixRepresentation generatorA * decode b34 = decode b35 :=
  sound atlasARows b34 b35 b35_valid b35_check

private theorem b_word4 :
    matrixRepresentation wordB * decode b28 = decode b35 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b29_step, b30_step, b31_step, b32_step, b33_step, b34_step, b35_step]

public theorem b_power5 :
    matrixRepresentation (wordB ^ 5) * decode b0 = decode b35 := by
  exact power_step wordB 4 _ _ _ b_power4 b_word4

end Lyons.OrderCertificate.PlaneTransport
