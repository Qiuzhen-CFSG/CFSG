module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport17

/-!
# Lyons plane transport through wordB, step 19

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 19 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b127_valid : valid b126 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b127_check : check atlasBRows b126 b127 = true := by
  decide +kernel

private theorem b127_step :
    matrixRepresentation generatorB * decode b126 = decode b127 :=
  sound atlasBRows b126 b127 b127_valid b127_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b128_valid : valid b127 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b128_check : check atlasBRows b127 b128 = true := by
  decide +kernel

private theorem b128_step :
    matrixRepresentation generatorB * decode b127 = decode b128 :=
  sound atlasBRows b127 b128 b128_valid b128_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b129_valid : valid b128 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b129_check : check atlasARows b128 b129 = true := by
  decide +kernel

private theorem b129_step :
    matrixRepresentation generatorA * decode b128 = decode b129 :=
  sound atlasARows b128 b129 b129_valid b129_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b130_valid : valid b129 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b130_check : check atlasBRows b129 b130 = true := by
  decide +kernel

private theorem b130_step :
    matrixRepresentation generatorB * decode b129 = decode b130 :=
  sound atlasBRows b129 b130 b130_valid b130_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b131_valid : valid b130 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b131_check : check atlasARows b130 b131 = true := by
  decide +kernel

private theorem b131_step :
    matrixRepresentation generatorA * decode b130 = decode b131 :=
  sound atlasARows b130 b131 b131_valid b131_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b132_valid : valid b131 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b132_check : check atlasBRows b131 b132 = true := by
  decide +kernel

private theorem b132_step :
    matrixRepresentation generatorB * decode b131 = decode b132 :=
  sound atlasBRows b131 b132 b132_valid b132_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b133_valid : valid b132 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b133_check : check atlasARows b132 b133 = true := by
  decide +kernel

private theorem b133_step :
    matrixRepresentation generatorA * decode b132 = decode b133 :=
  sound atlasARows b132 b133 b133_valid b133_check

private theorem b_word18 :
    matrixRepresentation wordB * decode b126 = decode b133 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b127_step, b128_step, b129_step, b130_step, b131_step, b132_step, b133_step]

public theorem b_power19 :
    matrixRepresentation (wordB ^ 19) * decode b0 = decode b133 := by
  exact power_step wordB 18 _ _ _ b_power18 b_word18

end Lyons.OrderCertificate.PlaneTransport
