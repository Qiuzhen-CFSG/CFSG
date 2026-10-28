module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport4

/-!
# Lyons plane transport through wordB, step 6

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 6 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b36_valid : valid b35 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b36_check : check atlasBRows b35 b36 = true := by
  decide +kernel

private theorem b36_step :
    matrixRepresentation generatorB * decode b35 = decode b36 :=
  sound atlasBRows b35 b36 b36_valid b36_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b37_valid : valid b36 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b37_check : check atlasBRows b36 b37 = true := by
  decide +kernel

private theorem b37_step :
    matrixRepresentation generatorB * decode b36 = decode b37 :=
  sound atlasBRows b36 b37 b37_valid b37_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b38_valid : valid b37 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b38_check : check atlasARows b37 b38 = true := by
  decide +kernel

private theorem b38_step :
    matrixRepresentation generatorA * decode b37 = decode b38 :=
  sound atlasARows b37 b38 b38_valid b38_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b39_valid : valid b38 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b39_check : check atlasBRows b38 b39 = true := by
  decide +kernel

private theorem b39_step :
    matrixRepresentation generatorB * decode b38 = decode b39 :=
  sound atlasBRows b38 b39 b39_valid b39_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b40_valid : valid b39 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b40_check : check atlasARows b39 b40 = true := by
  decide +kernel

private theorem b40_step :
    matrixRepresentation generatorA * decode b39 = decode b40 :=
  sound atlasARows b39 b40 b40_valid b40_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b41_valid : valid b40 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b41_check : check atlasBRows b40 b41 = true := by
  decide +kernel

private theorem b41_step :
    matrixRepresentation generatorB * decode b40 = decode b41 :=
  sound atlasBRows b40 b41 b41_valid b41_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b42_valid : valid b41 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b42_check : check atlasARows b41 b42 = true := by
  decide +kernel

private theorem b42_step :
    matrixRepresentation generatorA * decode b41 = decode b42 :=
  sound atlasARows b41 b42 b42_valid b42_check

private theorem b_word5 :
    matrixRepresentation wordB * decode b35 = decode b42 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b36_step, b37_step, b38_step, b39_step, b40_step, b41_step, b42_step]

public theorem b_power6 :
    matrixRepresentation (wordB ^ 6) * decode b0 = decode b42 := by
  exact power_step wordB 5 _ _ _ b_power5 b_word5

end Lyons.OrderCertificate.PlaneTransport
