module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.CTransport0

/-!
# Lyons plane transport through wordC, step 2

Kernel-checked elementary transports through the literal word `ABABABBAB`.
The accumulated identity records power number 2 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c10_valid : valid c9 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c10_check : check atlasBRows c9 c10 = true := by
  decide +kernel

private theorem c10_step :
    matrixRepresentation generatorB * decode c9 = decode c10 :=
  sound atlasBRows c9 c10 c10_valid c10_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c11_valid : valid c10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c11_check : check atlasARows c10 c11 = true := by
  decide +kernel

private theorem c11_step :
    matrixRepresentation generatorA * decode c10 = decode c11 :=
  sound atlasARows c10 c11 c11_valid c11_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c12_valid : valid c11 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c12_check : check atlasBRows c11 c12 = true := by
  decide +kernel

private theorem c12_step :
    matrixRepresentation generatorB * decode c11 = decode c12 :=
  sound atlasBRows c11 c12 c12_valid c12_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c13_valid : valid c12 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c13_check : check atlasBRows c12 c13 = true := by
  decide +kernel

private theorem c13_step :
    matrixRepresentation generatorB * decode c12 = decode c13 :=
  sound atlasBRows c12 c13 c13_valid c13_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c14_valid : valid c13 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c14_check : check atlasARows c13 c14 = true := by
  decide +kernel

private theorem c14_step :
    matrixRepresentation generatorA * decode c13 = decode c14 :=
  sound atlasARows c13 c14 c14_valid c14_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c15_valid : valid c14 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c15_check : check atlasBRows c14 c15 = true := by
  decide +kernel

private theorem c15_step :
    matrixRepresentation generatorB * decode c14 = decode c15 :=
  sound atlasBRows c14 c15 c15_valid c15_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c16_valid : valid c15 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c16_check : check atlasARows c15 c16 = true := by
  decide +kernel

private theorem c16_step :
    matrixRepresentation generatorA * decode c15 = decode c16 :=
  sound atlasARows c15 c16 c16_valid c16_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c17_valid : valid c16 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c17_check : check atlasBRows c16 c17 = true := by
  decide +kernel

private theorem c17_step :
    matrixRepresentation generatorB * decode c16 = decode c17 :=
  sound atlasBRows c16 c17 c17_valid c17_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c18_valid : valid c17 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c18_check : check atlasARows c17 c18 = true := by
  decide +kernel

private theorem c18_step :
    matrixRepresentation generatorA * decode c17 = decode c18 :=
  sound atlasARows c17 c18 c18_valid c18_check

private theorem c_word1 :
    matrixRepresentation wordC * decode c9 = decode c18 := by
  simp only [wordC, wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [c10_step, c11_step, c12_step, c13_step, c14_step, c15_step, c16_step, c17_step, c18_step]

public theorem c_power2 :
    matrixRepresentation (wordC ^ 2) * decode c0 = decode c18 := by
  exact power_step wordC 1 _ _ _ c_power1 c_word1

end Lyons.OrderCertificate.PlaneTransport
