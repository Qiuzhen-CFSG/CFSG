module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport21

/-!
# Lyons plane transport through wordB, step 23

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 23 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b155_valid : valid b154 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b155_check : check atlasBRows b154 b155 = true := by
  decide +kernel

private theorem b155_step :
    matrixRepresentation generatorB * decode b154 = decode b155 :=
  sound atlasBRows b154 b155 b155_valid b155_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b156_valid : valid b155 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b156_check : check atlasBRows b155 b156 = true := by
  decide +kernel

private theorem b156_step :
    matrixRepresentation generatorB * decode b155 = decode b156 :=
  sound atlasBRows b155 b156 b156_valid b156_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b157_valid : valid b156 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b157_check : check atlasARows b156 b157 = true := by
  decide +kernel

private theorem b157_step :
    matrixRepresentation generatorA * decode b156 = decode b157 :=
  sound atlasARows b156 b157 b157_valid b157_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b158_valid : valid b157 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b158_check : check atlasBRows b157 b158 = true := by
  decide +kernel

private theorem b158_step :
    matrixRepresentation generatorB * decode b157 = decode b158 :=
  sound atlasBRows b157 b158 b158_valid b158_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b159_valid : valid b158 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b159_check : check atlasARows b158 b159 = true := by
  decide +kernel

private theorem b159_step :
    matrixRepresentation generatorA * decode b158 = decode b159 :=
  sound atlasARows b158 b159 b159_valid b159_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b160_valid : valid b159 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b160_check : check atlasBRows b159 b160 = true := by
  decide +kernel

private theorem b160_step :
    matrixRepresentation generatorB * decode b159 = decode b160 :=
  sound atlasBRows b159 b160 b160_valid b160_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b161_valid : valid b160 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b161_check : check atlasARows b160 b161 = true := by
  decide +kernel

private theorem b161_step :
    matrixRepresentation generatorA * decode b160 = decode b161 :=
  sound atlasARows b160 b161 b161_valid b161_check

private theorem b_word22 :
    matrixRepresentation wordB * decode b154 = decode b161 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b155_step, b156_step, b157_step, b158_step, b159_step, b160_step, b161_step]

public theorem b_power23 :
    matrixRepresentation (wordB ^ 23) * decode b0 = decode b161 := by
  exact power_step wordB 22 _ _ _ b_power22 b_word22

end Lyons.OrderCertificate.PlaneTransport
