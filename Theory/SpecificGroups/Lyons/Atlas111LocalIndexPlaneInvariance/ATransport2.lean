module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.ATransport1

/-!
# Lyons plane transport through wordA, step 3

Kernel-checked elementary transports through the literal word `ABABBB`.
The accumulated identity records power number 3 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a13_valid : valid a12 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a13_check : check atlasBRows a12 a13 = true := by
  decide +kernel

private theorem a13_step :
    matrixRepresentation generatorB * decode a12 = decode a13 :=
  sound atlasBRows a12 a13 a13_valid a13_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a14_valid : valid a13 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a14_check : check atlasBRows a13 a14 = true := by
  decide +kernel

private theorem a14_step :
    matrixRepresentation generatorB * decode a13 = decode a14 :=
  sound atlasBRows a13 a14 a14_valid a14_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a15_valid : valid a14 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a15_check : check atlasBRows a14 a15 = true := by
  decide +kernel

private theorem a15_step :
    matrixRepresentation generatorB * decode a14 = decode a15 :=
  sound atlasBRows a14 a15 a15_valid a15_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a16_valid : valid a15 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a16_check : check atlasARows a15 a16 = true := by
  decide +kernel

private theorem a16_step :
    matrixRepresentation generatorA * decode a15 = decode a16 :=
  sound atlasARows a15 a16 a16_valid a16_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a17_valid : valid a16 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a17_check : check atlasBRows a16 a17 = true := by
  decide +kernel

private theorem a17_step :
    matrixRepresentation generatorB * decode a16 = decode a17 :=
  sound atlasBRows a16 a17 a17_valid a17_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a18_valid : valid a17 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a18_check : check atlasARows a17 a18 = true := by
  decide +kernel

private theorem a18_step :
    matrixRepresentation generatorA * decode a17 = decode a18 :=
  sound atlasARows a17 a18 a18_valid a18_check

private theorem a_word2 :
    matrixRepresentation wordA * decode a12 = decode a18 := by
  simp only [wordA, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [a13_step, a14_step, a15_step, a16_step, a17_step, a18_step]

public theorem a_power3 :
    matrixRepresentation (wordA ^ 3) * decode a0 = decode a18 := by
  exact power_step wordA 2 _ _ _ a_power2 a_word2

end Lyons.OrderCertificate.PlaneTransport
