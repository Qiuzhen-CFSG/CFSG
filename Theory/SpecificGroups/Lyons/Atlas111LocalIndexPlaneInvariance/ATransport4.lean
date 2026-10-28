module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.ATransport3

/-!
# Lyons plane transport through wordA, step 5

Kernel-checked elementary transports through the literal word `ABABBB`.
The accumulated identity records power number 5 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a25_valid : valid a24 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a25_check : check atlasBRows a24 a25 = true := by
  decide +kernel

private theorem a25_step :
    matrixRepresentation generatorB * decode a24 = decode a25 :=
  sound atlasBRows a24 a25 a25_valid a25_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a26_valid : valid a25 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a26_check : check atlasBRows a25 a26 = true := by
  decide +kernel

private theorem a26_step :
    matrixRepresentation generatorB * decode a25 = decode a26 :=
  sound atlasBRows a25 a26 a26_valid a26_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a27_valid : valid a26 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a27_check : check atlasBRows a26 a27 = true := by
  decide +kernel

private theorem a27_step :
    matrixRepresentation generatorB * decode a26 = decode a27 :=
  sound atlasBRows a26 a27 a27_valid a27_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a28_valid : valid a27 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a28_check : check atlasARows a27 a28 = true := by
  decide +kernel

private theorem a28_step :
    matrixRepresentation generatorA * decode a27 = decode a28 :=
  sound atlasARows a27 a28 a28_valid a28_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a29_valid : valid a28 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a29_check : check atlasBRows a28 a29 = true := by
  decide +kernel

private theorem a29_step :
    matrixRepresentation generatorB * decode a28 = decode a29 :=
  sound atlasBRows a28 a29 a29_valid a29_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a30_valid : valid a29 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem a30_check : check atlasARows a29 a30 = true := by
  decide +kernel

private theorem a30_step :
    matrixRepresentation generatorA * decode a29 = decode a30 :=
  sound atlasARows a29 a30 a30_valid a30_check

private theorem a_word4 :
    matrixRepresentation wordA * decode a24 = decode a30 := by
  simp only [wordA, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [a25_step, a26_step, a27_step, a28_step, a29_step, a30_step]

public theorem a_power5 :
    matrixRepresentation (wordA ^ 5) * decode a0 = decode a30 := by
  exact power_step wordA 4 _ _ _ a_power4 a_word4

end Lyons.OrderCertificate.PlaneTransport
