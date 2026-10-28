module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.ATransport5

/-!
# Lyons plane transport through wordA, step 7

Kernel-checked elementary transports through the literal word `ABABBB`.
The accumulated identity records power number 7 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a37_valid : valid a36 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a37_check : check atlasBRows a36 a37 = true := by
  decide +kernel

private theorem a37_step :
    matrixRepresentation generatorB * decode a36 = decode a37 :=
  sound atlasBRows a36 a37 a37_valid a37_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a38_valid : valid a37 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a38_check : check atlasBRows a37 a38 = true := by
  decide +kernel

private theorem a38_step :
    matrixRepresentation generatorB * decode a37 = decode a38 :=
  sound atlasBRows a37 a38 a38_valid a38_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a39_valid : valid a38 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a39_check : check atlasBRows a38 a39 = true := by
  decide +kernel

private theorem a39_step :
    matrixRepresentation generatorB * decode a38 = decode a39 :=
  sound atlasBRows a38 a39 a39_valid a39_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a40_valid : valid a39 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a40_check : check atlasARows a39 a40 = true := by
  decide +kernel

private theorem a40_step :
    matrixRepresentation generatorA * decode a39 = decode a40 :=
  sound atlasARows a39 a40 a40_valid a40_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a41_valid : valid a40 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a41_check : check atlasBRows a40 a41 = true := by
  decide +kernel

private theorem a41_step :
    matrixRepresentation generatorB * decode a40 = decode a41 :=
  sound atlasBRows a40 a41 a41_valid a41_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a42_valid : valid a41 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a42_check : check atlasARows a41 a42 = true := by
  decide +kernel

private theorem a42_step :
    matrixRepresentation generatorA * decode a41 = decode a42 :=
  sound atlasARows a41 a42 a42_valid a42_check

private theorem a_word6 :
    matrixRepresentation wordA * decode a36 = decode a42 := by
  simp only [wordA, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [a37_step, a38_step, a39_step, a40_step, a41_step, a42_step]

public theorem a_power7 :
    matrixRepresentation (wordA ^ 7) * decode a0 = decode a42 := by
  exact power_step wordA 6 _ _ _ a_power6 a_word6

end Lyons.OrderCertificate.PlaneTransport
