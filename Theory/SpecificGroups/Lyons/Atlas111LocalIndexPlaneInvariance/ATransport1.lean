module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.ATransport0

/-!
# Lyons plane transport through wordA, step 2

Kernel-checked elementary transports through the literal word `ABABBB`.
The accumulated identity records power number 2 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a7_valid : valid a6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a7_check : check atlasBRows a6 a7 = true := by
  decide +kernel

private theorem a7_step :
    matrixRepresentation generatorB * decode a6 = decode a7 :=
  sound atlasBRows a6 a7 a7_valid a7_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a8_valid : valid a7 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a8_check : check atlasBRows a7 a8 = true := by
  decide +kernel

private theorem a8_step :
    matrixRepresentation generatorB * decode a7 = decode a8 :=
  sound atlasBRows a7 a8 a8_valid a8_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a9_valid : valid a8 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a9_check : check atlasBRows a8 a9 = true := by
  decide +kernel

private theorem a9_step :
    matrixRepresentation generatorB * decode a8 = decode a9 :=
  sound atlasBRows a8 a9 a9_valid a9_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a10_valid : valid a9 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a10_check : check atlasARows a9 a10 = true := by
  decide +kernel

private theorem a10_step :
    matrixRepresentation generatorA * decode a9 = decode a10 :=
  sound atlasARows a9 a10 a10_valid a10_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a11_valid : valid a10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a11_check : check atlasBRows a10 a11 = true := by
  decide +kernel

private theorem a11_step :
    matrixRepresentation generatorB * decode a10 = decode a11 :=
  sound atlasBRows a10 a11 a11_valid a11_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a12_valid : valid a11 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a12_check : check atlasARows a11 a12 = true := by
  decide +kernel

private theorem a12_step :
    matrixRepresentation generatorA * decode a11 = decode a12 :=
  sound atlasARows a11 a12 a12_valid a12_check

private theorem a_word1 :
    matrixRepresentation wordA * decode a6 = decode a12 := by
  simp only [wordA, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [a7_step, a8_step, a9_step, a10_step, a11_step, a12_step]

public theorem a_power2 :
    matrixRepresentation (wordA ^ 2) * decode a0 = decode a12 := by
  exact power_step wordA 1 _ _ _ a_power1 a_word1

end Lyons.OrderCertificate.PlaneTransport
