module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport18

/-!
# Lyons plane transport through wordB, step 20

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 20 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b134_valid : valid b133 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b134_check : check atlasBRows b133 b134 = true := by
  decide +kernel

private theorem b134_step :
    matrixRepresentation generatorB * decode b133 = decode b134 :=
  sound atlasBRows b133 b134 b134_valid b134_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b135_valid : valid b134 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b135_check : check atlasBRows b134 b135 = true := by
  decide +kernel

private theorem b135_step :
    matrixRepresentation generatorB * decode b134 = decode b135 :=
  sound atlasBRows b134 b135 b135_valid b135_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b136_valid : valid b135 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b136_check : check atlasARows b135 b136 = true := by
  decide +kernel

private theorem b136_step :
    matrixRepresentation generatorA * decode b135 = decode b136 :=
  sound atlasARows b135 b136 b136_valid b136_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b137_valid : valid b136 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b137_check : check atlasBRows b136 b137 = true := by
  decide +kernel

private theorem b137_step :
    matrixRepresentation generatorB * decode b136 = decode b137 :=
  sound atlasBRows b136 b137 b137_valid b137_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b138_valid : valid b137 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b138_check : check atlasARows b137 b138 = true := by
  decide +kernel

private theorem b138_step :
    matrixRepresentation generatorA * decode b137 = decode b138 :=
  sound atlasARows b137 b138 b138_valid b138_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b139_valid : valid b138 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b139_check : check atlasBRows b138 b139 = true := by
  decide +kernel

private theorem b139_step :
    matrixRepresentation generatorB * decode b138 = decode b139 :=
  sound atlasBRows b138 b139 b139_valid b139_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b140_valid : valid b139 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b140_check : check atlasARows b139 b140 = true := by
  decide +kernel

private theorem b140_step :
    matrixRepresentation generatorA * decode b139 = decode b140 :=
  sound atlasARows b139 b140 b140_valid b140_check

private theorem b_word19 :
    matrixRepresentation wordB * decode b133 = decode b140 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b134_step, b135_step, b136_step, b137_step, b138_step, b139_step, b140_step]

public theorem b_power20 :
    matrixRepresentation (wordB ^ 20) * decode b0 = decode b140 := by
  exact power_step wordB 19 _ _ _ b_power19 b_word19

end Lyons.OrderCertificate.PlaneTransport
