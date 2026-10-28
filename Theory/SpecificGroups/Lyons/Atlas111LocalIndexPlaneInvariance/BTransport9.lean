module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport8

/-!
# Lyons plane transport through wordB, step 10

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 10 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b64_valid : valid b63 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b64_check : check atlasBRows b63 b64 = true := by
  decide +kernel

private theorem b64_step :
    matrixRepresentation generatorB * decode b63 = decode b64 :=
  sound atlasBRows b63 b64 b64_valid b64_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b65_valid : valid b64 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b65_check : check atlasBRows b64 b65 = true := by
  decide +kernel

private theorem b65_step :
    matrixRepresentation generatorB * decode b64 = decode b65 :=
  sound atlasBRows b64 b65 b65_valid b65_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b66_valid : valid b65 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b66_check : check atlasARows b65 b66 = true := by
  decide +kernel

private theorem b66_step :
    matrixRepresentation generatorA * decode b65 = decode b66 :=
  sound atlasARows b65 b66 b66_valid b66_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b67_valid : valid b66 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b67_check : check atlasBRows b66 b67 = true := by
  decide +kernel

private theorem b67_step :
    matrixRepresentation generatorB * decode b66 = decode b67 :=
  sound atlasBRows b66 b67 b67_valid b67_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b68_valid : valid b67 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b68_check : check atlasARows b67 b68 = true := by
  decide +kernel

private theorem b68_step :
    matrixRepresentation generatorA * decode b67 = decode b68 :=
  sound atlasARows b67 b68 b68_valid b68_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b69_valid : valid b68 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b69_check : check atlasBRows b68 b69 = true := by
  decide +kernel

private theorem b69_step :
    matrixRepresentation generatorB * decode b68 = decode b69 :=
  sound atlasBRows b68 b69 b69_valid b69_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b70_valid : valid b69 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b70_check : check atlasARows b69 b70 = true := by
  decide +kernel

private theorem b70_step :
    matrixRepresentation generatorA * decode b69 = decode b70 :=
  sound atlasARows b69 b70 b70_valid b70_check

private theorem b_word9 :
    matrixRepresentation wordB * decode b63 = decode b70 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b64_step, b65_step, b66_step, b67_step, b68_step, b69_step, b70_step]

public theorem b_power10 :
    matrixRepresentation (wordB ^ 10) * decode b0 = decode b70 := by
  exact power_step wordB 9 _ _ _ b_power9 b_word9

end Lyons.OrderCertificate.PlaneTransport
