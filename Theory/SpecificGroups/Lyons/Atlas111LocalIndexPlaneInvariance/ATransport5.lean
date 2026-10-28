module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.ATransport4

/-!
# Lyons plane transport through wordA, step 6

Kernel-checked elementary transports through the literal word `ABABBB`.
The accumulated identity records power number 6 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a31_valid : valid a30 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a31_check : check atlasBRows a30 a31 = true := by
  decide +kernel

private theorem a31_step :
    matrixRepresentation generatorB * decode a30 = decode a31 :=
  sound atlasBRows a30 a31 a31_valid a31_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a32_valid : valid a31 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a32_check : check atlasBRows a31 a32 = true := by
  decide +kernel

private theorem a32_step :
    matrixRepresentation generatorB * decode a31 = decode a32 :=
  sound atlasBRows a31 a32 a32_valid a32_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a33_valid : valid a32 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a33_check : check atlasBRows a32 a33 = true := by
  decide +kernel

private theorem a33_step :
    matrixRepresentation generatorB * decode a32 = decode a33 :=
  sound atlasBRows a32 a33 a33_valid a33_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a34_valid : valid a33 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a34_check : check atlasARows a33 a34 = true := by
  decide +kernel

private theorem a34_step :
    matrixRepresentation generatorA * decode a33 = decode a34 :=
  sound atlasARows a33 a34 a34_valid a34_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a35_valid : valid a34 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a35_check : check atlasBRows a34 a35 = true := by
  decide +kernel

private theorem a35_step :
    matrixRepresentation generatorB * decode a34 = decode a35 :=
  sound atlasBRows a34 a35 a35_valid a35_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a36_valid : valid a35 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a36_check : check atlasARows a35 a36 = true := by
  decide +kernel

private theorem a36_step :
    matrixRepresentation generatorA * decode a35 = decode a36 :=
  sound atlasARows a35 a36 a36_valid a36_check

private theorem a_word5 :
    matrixRepresentation wordA * decode a30 = decode a36 := by
  simp only [wordA, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [a31_step, a32_step, a33_step, a34_step, a35_step, a36_step]

public theorem a_power6 :
    matrixRepresentation (wordA ^ 6) * decode a0 = decode a36 := by
  exact power_step wordA 5 _ _ _ a_power5 a_word5

end Lyons.OrderCertificate.PlaneTransport
