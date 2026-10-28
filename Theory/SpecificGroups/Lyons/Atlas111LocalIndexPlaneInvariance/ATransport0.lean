module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.Data
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.Words

/-!
# Lyons plane transport through wordA, step 1

Kernel-checked elementary transports through the literal word `ABABBB`.
The accumulated identity records power number 1 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a1_valid : valid a0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a1_check : check atlasBRows a0 a1 = true := by
  decide +kernel

private theorem a1_step :
    matrixRepresentation generatorB * decode a0 = decode a1 :=
  sound atlasBRows a0 a1 a1_valid a1_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a2_valid : valid a1 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a2_check : check atlasBRows a1 a2 = true := by
  decide +kernel

private theorem a2_step :
    matrixRepresentation generatorB * decode a1 = decode a2 :=
  sound atlasBRows a1 a2 a2_valid a2_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a3_valid : valid a2 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a3_check : check atlasBRows a2 a3 = true := by
  decide +kernel

private theorem a3_step :
    matrixRepresentation generatorB * decode a2 = decode a3 :=
  sound atlasBRows a2 a3 a3_valid a3_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a4_valid : valid a3 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a4_check : check atlasARows a3 a4 = true := by
  decide +kernel

private theorem a4_step :
    matrixRepresentation generatorA * decode a3 = decode a4 :=
  sound atlasARows a3 a4 a4_valid a4_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a5_valid : valid a4 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a5_check : check atlasBRows a4 a5 = true := by
  decide +kernel

private theorem a5_step :
    matrixRepresentation generatorB * decode a4 = decode a5 :=
  sound atlasBRows a4 a5 a5_valid a5_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a6_valid : valid a5 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a6_check : check atlasARows a5 a6 = true := by
  decide +kernel

private theorem a6_step :
    matrixRepresentation generatorA * decode a5 = decode a6 :=
  sound atlasARows a5 a6 a6_valid a6_check

private theorem a_word0 :
    matrixRepresentation wordA * decode a0 = decode a6 := by
  simp only [wordA, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [a1_step, a2_step, a3_step, a4_step, a5_step, a6_step]

public theorem a_power1 :
    matrixRepresentation (wordA ^ 1) * decode a0 = decode a6 := by
  simpa only [pow_one] using a_word0

end Lyons.OrderCertificate.PlaneTransport
