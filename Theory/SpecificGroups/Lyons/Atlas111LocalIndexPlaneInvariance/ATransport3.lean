module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.ATransport2

/-!
# Lyons plane transport through wordA, step 4

Kernel-checked elementary transports through the literal word `ABABBB`.
The accumulated identity records power number 4 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a19_valid : valid a18 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a19_check : check atlasBRows a18 a19 = true := by
  decide +kernel

private theorem a19_step :
    matrixRepresentation generatorB * decode a18 = decode a19 :=
  sound atlasBRows a18 a19 a19_valid a19_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a20_valid : valid a19 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a20_check : check atlasBRows a19 a20 = true := by
  decide +kernel

private theorem a20_step :
    matrixRepresentation generatorB * decode a19 = decode a20 :=
  sound atlasBRows a19 a20 a20_valid a20_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a21_valid : valid a20 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a21_check : check atlasBRows a20 a21 = true := by
  decide +kernel

private theorem a21_step :
    matrixRepresentation generatorB * decode a20 = decode a21 :=
  sound atlasBRows a20 a21 a21_valid a21_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a22_valid : valid a21 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a22_check : check atlasARows a21 a22 = true := by
  decide +kernel

private theorem a22_step :
    matrixRepresentation generatorA * decode a21 = decode a22 :=
  sound atlasARows a21 a22 a22_valid a22_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a23_valid : valid a22 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a23_check : check atlasBRows a22 a23 = true := by
  decide +kernel

private theorem a23_step :
    matrixRepresentation generatorB * decode a22 = decode a23 :=
  sound atlasBRows a22 a23 a23_valid a23_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a24_valid : valid a23 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a24_check : check atlasARows a23 a24 = true := by
  decide +kernel

private theorem a24_step :
    matrixRepresentation generatorA * decode a23 = decode a24 :=
  sound atlasARows a23 a24 a24_valid a24_check

private theorem a_word3 :
    matrixRepresentation wordA * decode a18 = decode a24 := by
  simp only [wordA, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [a19_step, a20_step, a21_step, a22_step, a23_step, a24_step]

public theorem a_power4 :
    matrixRepresentation (wordA ^ 4) * decode a0 = decode a24 := by
  exact power_step wordA 3 _ _ _ a_power3 a_word3

end Lyons.OrderCertificate.PlaneTransport
