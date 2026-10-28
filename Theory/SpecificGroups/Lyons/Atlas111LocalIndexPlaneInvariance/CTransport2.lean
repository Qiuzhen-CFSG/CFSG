module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.CTransport1

/-!
# Lyons plane transport through wordC, step 3

Kernel-checked elementary transports through the literal word `ABABABBAB`.
The accumulated identity records power number 3 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c19_valid : valid c18 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c19_check : check atlasBRows c18 c19 = true := by
  decide +kernel

private theorem c19_step :
    matrixRepresentation generatorB * decode c18 = decode c19 :=
  sound atlasBRows c18 c19 c19_valid c19_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c20_valid : valid c19 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c20_check : check atlasARows c19 c20 = true := by
  decide +kernel

private theorem c20_step :
    matrixRepresentation generatorA * decode c19 = decode c20 :=
  sound atlasARows c19 c20 c20_valid c20_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c21_valid : valid c20 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c21_check : check atlasBRows c20 c21 = true := by
  decide +kernel

private theorem c21_step :
    matrixRepresentation generatorB * decode c20 = decode c21 :=
  sound atlasBRows c20 c21 c21_valid c21_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c22_valid : valid c21 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c22_check : check atlasBRows c21 c22 = true := by
  decide +kernel

private theorem c22_step :
    matrixRepresentation generatorB * decode c21 = decode c22 :=
  sound atlasBRows c21 c22 c22_valid c22_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c23_valid : valid c22 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c23_check : check atlasARows c22 c23 = true := by
  decide +kernel

private theorem c23_step :
    matrixRepresentation generatorA * decode c22 = decode c23 :=
  sound atlasARows c22 c23 c23_valid c23_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c24_valid : valid c23 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c24_check : check atlasBRows c23 c24 = true := by
  decide +kernel

private theorem c24_step :
    matrixRepresentation generatorB * decode c23 = decode c24 :=
  sound atlasBRows c23 c24 c24_valid c24_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c25_valid : valid c24 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c25_check : check atlasARows c24 c25 = true := by
  decide +kernel

private theorem c25_step :
    matrixRepresentation generatorA * decode c24 = decode c25 :=
  sound atlasARows c24 c25 c25_valid c25_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c26_valid : valid c25 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c26_check : check atlasBRows c25 c26 = true := by
  decide +kernel

private theorem c26_step :
    matrixRepresentation generatorB * decode c25 = decode c26 :=
  sound atlasBRows c25 c26 c26_valid c26_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c27_valid : valid c26 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c27_check : check atlasARows c26 c27 = true := by
  decide +kernel

private theorem c27_step :
    matrixRepresentation generatorA * decode c26 = decode c27 :=
  sound atlasARows c26 c27 c27_valid c27_check

private theorem c_word2 :
    matrixRepresentation wordC * decode c18 = decode c27 := by
  simp only [wordC, wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [c19_step, c20_step, c21_step, c22_step, c23_step, c24_step, c25_step, c26_step, c27_step]

public theorem c_power3 :
    matrixRepresentation (wordC ^ 3) * decode c0 = decode c27 := by
  exact power_step wordC 2 _ _ _ c_power2 c_word2

end Lyons.OrderCertificate.PlaneTransport
