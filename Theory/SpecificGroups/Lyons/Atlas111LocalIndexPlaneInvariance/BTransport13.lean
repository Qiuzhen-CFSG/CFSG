module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport12

/-!
# Lyons plane transport through wordB, step 14

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 14 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b92_valid : valid b91 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b92_check : check atlasBRows b91 b92 = true := by
  decide +kernel

private theorem b92_step :
    matrixRepresentation generatorB * decode b91 = decode b92 :=
  sound atlasBRows b91 b92 b92_valid b92_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b93_valid : valid b92 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b93_check : check atlasBRows b92 b93 = true := by
  decide +kernel

private theorem b93_step :
    matrixRepresentation generatorB * decode b92 = decode b93 :=
  sound atlasBRows b92 b93 b93_valid b93_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b94_valid : valid b93 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b94_check : check atlasARows b93 b94 = true := by
  decide +kernel

private theorem b94_step :
    matrixRepresentation generatorA * decode b93 = decode b94 :=
  sound atlasARows b93 b94 b94_valid b94_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b95_valid : valid b94 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b95_check : check atlasBRows b94 b95 = true := by
  decide +kernel

private theorem b95_step :
    matrixRepresentation generatorB * decode b94 = decode b95 :=
  sound atlasBRows b94 b95 b95_valid b95_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b96_valid : valid b95 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b96_check : check atlasARows b95 b96 = true := by
  decide +kernel

private theorem b96_step :
    matrixRepresentation generatorA * decode b95 = decode b96 :=
  sound atlasARows b95 b96 b96_valid b96_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b97_valid : valid b96 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b97_check : check atlasBRows b96 b97 = true := by
  decide +kernel

private theorem b97_step :
    matrixRepresentation generatorB * decode b96 = decode b97 :=
  sound atlasBRows b96 b97 b97_valid b97_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b98_valid : valid b97 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b98_check : check atlasARows b97 b98 = true := by
  decide +kernel

private theorem b98_step :
    matrixRepresentation generatorA * decode b97 = decode b98 :=
  sound atlasARows b97 b98 b98_valid b98_check

private theorem b_word13 :
    matrixRepresentation wordB * decode b91 = decode b98 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b92_step, b93_step, b94_step, b95_step, b96_step, b97_step, b98_step]

public theorem b_power14 :
    matrixRepresentation (wordB ^ 14) * decode b0 = decode b98 := by
  exact power_step wordB 13 _ _ _ b_power13 b_word13

end Lyons.OrderCertificate.PlaneTransport
