module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport23

/-!
# Lyons plane transport through wordB, step 25

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 25 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b169_valid : valid b168 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b169_check : check atlasBRows b168 b169 = true := by
  decide +kernel

private theorem b169_step :
    matrixRepresentation generatorB * decode b168 = decode b169 :=
  sound atlasBRows b168 b169 b169_valid b169_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b170_valid : valid b169 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b170_check : check atlasBRows b169 b170 = true := by
  decide +kernel

private theorem b170_step :
    matrixRepresentation generatorB * decode b169 = decode b170 :=
  sound atlasBRows b169 b170 b170_valid b170_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b171_valid : valid b170 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b171_check : check atlasARows b170 b171 = true := by
  decide +kernel

private theorem b171_step :
    matrixRepresentation generatorA * decode b170 = decode b171 :=
  sound atlasARows b170 b171 b171_valid b171_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b172_valid : valid b171 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b172_check : check atlasBRows b171 b172 = true := by
  decide +kernel

private theorem b172_step :
    matrixRepresentation generatorB * decode b171 = decode b172 :=
  sound atlasBRows b171 b172 b172_valid b172_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b173_valid : valid b172 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b173_check : check atlasARows b172 b173 = true := by
  decide +kernel

private theorem b173_step :
    matrixRepresentation generatorA * decode b172 = decode b173 :=
  sound atlasARows b172 b173 b173_valid b173_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b174_valid : valid b173 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b174_check : check atlasBRows b173 b174 = true := by
  decide +kernel

private theorem b174_step :
    matrixRepresentation generatorB * decode b173 = decode b174 :=
  sound atlasBRows b173 b174 b174_valid b174_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b175_valid : valid b174 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b175_check : check atlasARows b174 b175 = true := by
  decide +kernel

private theorem b175_step :
    matrixRepresentation generatorA * decode b174 = decode b175 :=
  sound atlasARows b174 b175 b175_valid b175_check

private theorem b_word24 :
    matrixRepresentation wordB * decode b168 = decode b175 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b169_step, b170_step, b171_step, b172_step, b173_step, b174_step, b175_step]

public theorem b_power25 :
    matrixRepresentation (wordB ^ 25) * decode b0 = decode b175 := by
  exact power_step wordB 24 _ _ _ b_power24 b_word24

end Lyons.OrderCertificate.PlaneTransport
