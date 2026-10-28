module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport6

/-!
# Lyons plane transport through wordB, step 8

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 8 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b50_valid : valid b49 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b50_check : check atlasBRows b49 b50 = true := by
  decide +kernel

private theorem b50_step :
    matrixRepresentation generatorB * decode b49 = decode b50 :=
  sound atlasBRows b49 b50 b50_valid b50_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b51_valid : valid b50 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b51_check : check atlasBRows b50 b51 = true := by
  decide +kernel

private theorem b51_step :
    matrixRepresentation generatorB * decode b50 = decode b51 :=
  sound atlasBRows b50 b51 b51_valid b51_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b52_valid : valid b51 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b52_check : check atlasARows b51 b52 = true := by
  decide +kernel

private theorem b52_step :
    matrixRepresentation generatorA * decode b51 = decode b52 :=
  sound atlasARows b51 b52 b52_valid b52_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b53_valid : valid b52 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b53_check : check atlasBRows b52 b53 = true := by
  decide +kernel

private theorem b53_step :
    matrixRepresentation generatorB * decode b52 = decode b53 :=
  sound atlasBRows b52 b53 b53_valid b53_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b54_valid : valid b53 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b54_check : check atlasARows b53 b54 = true := by
  decide +kernel

private theorem b54_step :
    matrixRepresentation generatorA * decode b53 = decode b54 :=
  sound atlasARows b53 b54 b54_valid b54_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b55_valid : valid b54 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b55_check : check atlasBRows b54 b55 = true := by
  decide +kernel

private theorem b55_step :
    matrixRepresentation generatorB * decode b54 = decode b55 :=
  sound atlasBRows b54 b55 b55_valid b55_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b56_valid : valid b55 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b56_check : check atlasARows b55 b56 = true := by
  decide +kernel

private theorem b56_step :
    matrixRepresentation generatorA * decode b55 = decode b56 :=
  sound atlasARows b55 b56 b56_valid b56_check

private theorem b_word7 :
    matrixRepresentation wordB * decode b49 = decode b56 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b50_step, b51_step, b52_step, b53_step, b54_step, b55_step, b56_step]

public theorem b_power8 :
    matrixRepresentation (wordB ^ 8) * decode b0 = decode b56 := by
  exact power_step wordB 7 _ _ _ b_power7 b_word7

end Lyons.OrderCertificate.PlaneTransport
